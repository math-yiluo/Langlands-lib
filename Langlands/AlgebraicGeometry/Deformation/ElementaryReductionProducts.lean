import Langlands.AlgebraicGeometry.Deformation.ElementaryLiftPointed

/-! # Chosen reductions of fibre products and their maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections.Reduction

open SquareZeroAffinePairs
open ElementaryLiftCech (baseReduction)
open Picard.FieldTwoAxisH1Injectivity (prodOpen)

section Products

variable {S : Scheme.{u}} {Y Z : Over S}

/-- The chosen product in the slice category has the fibre product square as its underlying square. -/
lemma product_isPullback (Y Z : Over S) :
    IsPullback (fst Y Z).left (snd Y Z).left Y.hom Z.hom :=
  IsPullback.of_hasPullback _ _

/-- Map of the underlying fibre products induced by maps from their two factors. -/
def productMap {T : Scheme.{u}} {Y' Z' : Over T}
    (y : Y'.left ⟶ Y.left) (z : Z'.left ⟶ Z.left) (t : T ⟶ S)
    (hy : y ≫ Y.hom = Y'.hom ≫ t) (hz : z ≫ Z.hom = Z'.hom ≫ t) :
    (Y' ⊗ Z').left ⟶ (Y ⊗ Z).left :=
  (product_isPullback Y Z).lift ((fst Y' Z').left ≫ y) ((snd Y' Z').left ≫ z) (by
    rw [Category.assoc, Category.assoc, hy, hz, ← Category.assoc, ← Category.assoc,
      (product_isPullback Y' Z').w])

variable {T : Scheme.{u}} {Y' Z' : Over T} {y : Y'.left ⟶ Y.left} {z : Z'.left ⟶ Z.left}
    {t : T ⟶ S} (hy : IsPullback y Y'.hom Y.hom t) (hz : IsPullback z Z'.hom Z.hom t)

/-- Products of chosen base changes are base changes of the products. -/
lemma productMap_isPullback : IsPullback (productMap y z t hy.w hz.w) (Y' ⊗ Z').hom (Y ⊗ Z).hom t := by
  let p := product_isPullback Y Z
  let q := product_isPullback Y' Z'
  let k := productMap y z t hy.w hz.w
  have hk₁ : k ≫ (fst Y Z).left = (fst Y' Z').left ≫ y := p.lift_fst _ _ _
  have hk₂ : k ≫ (snd Y Z).left = (snd Y' Z').left ≫ z := p.lift_snd _ _ _
  have hk : k ≫ (Y ⊗ Z).hom = (Y' ⊗ Z').hom ≫ t := by
    change k ≫ (fst Y Z).left ≫ Y.hom = ((fst Y' Z').left ≫ Y'.hom) ≫ t
    rw [← Category.assoc, hk₁, Category.assoc, hy.w, Category.assoc]
  let a (c : PullbackCone (Y ⊗ Z).hom t) : c.pt ⟶ Y'.left :=
    hy.lift (c.fst ≫ (fst Y Z).left) c.snd (by rw [Category.assoc]; exact c.condition)
  let b (c : PullbackCone (Y ⊗ Z).hom t) : c.pt ⟶ Z'.left :=
    hz.lift (c.fst ≫ (snd Y Z).left) c.snd (by
      rw [Category.assoc, ← p.w]; exact c.condition)
  let j (c : PullbackCone (Y ⊗ Z).hom t) := q.lift (a c) (b c) (by simp [a, b])
  have j₁ (c : PullbackCone (Y ⊗ Z).hom t) : j c ≫ (fst Y' Z').left = a c := q.lift_fst _ _ _
  have j₂ (c : PullbackCone (Y ⊗ Z).hom t) : j c ≫ (snd Y' Z').left = b c := q.lift_snd _ _ _
  apply IsPullback.of_isLimit' ⟨hk⟩
  refine PullbackCone.IsLimit.mk hk j (fun c ↦ p.hom_ext ?_ ?_) (fun c ↦ ?_) (fun c d h₁ h₂ ↦ ?_)
  · rw [Category.assoc, hk₁, ← Category.assoc, j₁]
    exact hy.lift_fst _ _ _
  · rw [Category.assoc, hk₂, ← Category.assoc, j₂]
    exact hz.lift_fst _ _ _
  · change j c ≫ (fst Y' Z').left ≫ Y'.hom = c.snd
    rw [← Category.assoc, j₁]
    exact hy.lift_snd _ _ _
  · apply q.hom_ext
    · rw [j₁]
      apply hy.hom_ext
      · dsimp only [a]
        rw [hy.lift_fst, Category.assoc, ← hk₁, ← Category.assoc, h₁]
      · dsimp only [a]
        rw [hy.lift_snd, Category.assoc]
        exact h₂
    · rw [j₂]
      apply hz.hom_ext
      · dsimp only [b]
        rw [hz.lift_fst, Category.assoc, ← hk₂, ← Category.assoc, h₁]
      · dsimp only [b]
        rw [hz.lift_snd, Category.assoc, ← q.w]
        exact h₂

end Products

variable {R : Type u} [CommRing R] {L : Ideal R}
variable {W Y Z : Over (Spec (CommRingCat.of R))}

/-- Present the reduction of the product by the product of the reductions. -/
def fibreProduct (A : Reduction Y L) (B : Reduction Z L) : Reduction (Y ⊗ Z) L where
  obj := A.obj ⊗ B.obj
  toOriginal := productMap A.toOriginal B.toOriginal _ A.cartesian.w B.cartesian.w
  cartesian := productMap_isPullback A.cartesian B.cartesian

@[reassoc (attr := simp)] lemma fibreProduct_toOriginal_fst (A : Reduction Y L) (B : Reduction Z L) :
    (A.fibreProduct B).toOriginal ≫ (fst Y Z).left = (fst A.obj B.obj).left ≫ A.toOriginal :=
  (product_isPullback Y Z).lift_fst _ _ _

@[reassoc (attr := simp)] lemma fibreProduct_toOriginal_snd (A : Reduction Y L) (B : Reduction Z L) :
    (A.fibreProduct B).toOriginal ≫ (snd Y Z).left = (snd A.obj B.obj).left ≫ B.toOriginal :=
  (product_isPullback Y Z).lift_snd _ _ _

lemma map_eq_iff (D : Reduction W L) (A : Reduction Y L) (f g : W ⟶ Y) :
    D.map A f = D.map A g ↔ D.toOriginal ≫ f.left = D.toOriginal ≫ g.left := by
  constructor
  · intro h
    rw [← D.map_left_toOriginal f (B := A), ← D.map_left_toOriginal g (B := A), h]
  · intro h
    apply Over.OverMorphism.ext
    apply A.cartesian.hom_ext
    · simpa only [map_left_toOriginal] using h
    · rw [Over.w, Over.w]

@[simp] lemma map_fst (A : Reduction Y L) (B : Reduction Z L) :
    (A.fibreProduct B).map A (fst Y Z) = fst A.obj B.obj := by
  apply Over.OverMorphism.ext
  apply A.cartesian.hom_ext
  · rw [map_left_toOriginal, fibreProduct_toOriginal_fst]
  · rw [Over.w, Over.w]

@[simp] lemma map_snd (A : Reduction Y L) (B : Reduction Z L) :
    (A.fibreProduct B).map B (snd Y Z) = snd A.obj B.obj := by
  apply Over.OverMorphism.ext
  apply B.cartesian.hom_ext
  · rw [map_left_toOriginal, fibreProduct_toOriginal_snd]
  · rw [Over.w, Over.w]

@[simp] lemma map_lift (D : Reduction W L) (A : Reduction Y L) (B : Reduction Z L)
    (f : W ⟶ Y) (g : W ⟶ Z) :
    D.map (A.fibreProduct B) (lift f g) = lift (D.map A f) (D.map B g) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [← map_fst A B, ← map_comp, lift_fst, map_fst, lift_fst]
  · rw [← map_snd A B, ← map_comp, lift_snd, map_snd, lift_snd]

@[simp] lemma map_toUnit (A : Reduction Y L) :
    A.map (baseReduction L) (toUnit Y) = toUnit A.obj := by
  apply Over.OverMorphism.ext
  change (A.map (baseReduction L) (toUnit Y)).left = A.obj.hom
  exact (Category.comp_id _).symm.trans (Over.w (A.map (baseReduction L) (toUnit Y)))

/-- Preimage of a product chart is the product of the two preimage charts. -/
lemma fibreProduct_preimage_prodOpen (A : Reduction Y L) (B : Reduction Z L)
    (U : Y.left.Opens) (V : Z.left.Opens) :
    (A.fibreProduct B).toOriginal ⁻¹ᵁ prodOpen (fst Y Z).left (snd Y Z).left U V =
      prodOpen (fst A.obj B.obj).left (snd A.obj B.obj).left
        (A.toOriginal ⁻¹ᵁ U) (B.toOriginal ⁻¹ᵁ V) := by
  rw [prodOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    fibreProduct_toOriginal_fst, fibreProduct_toOriginal_snd]
  rfl

/-- A chosen reduction is isomorphic, in the slice, to the ordinary pullback. -/
def isoPullback (A : Reduction Y L) : A.obj ≅ (Reduction.pullback Y L).obj :=
  Over.isoMk A.cartesian.isoPullback (A.cartesian.isoPullback_hom_snd)

lemma isoPullback_naturality (A : Reduction Y L) (B : Reduction Z L) (f : Y ⟶ Z) :
    (A.map B f) ≫ B.isoPullback.hom =
      A.isoPullback.hom ≫ (Over.pullback (specMap (Ideal.Quotient.mk L))).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · let q := specMap (Ideal.Quotient.mk L)
    change ((A.map B f).left ≫ B.cartesian.isoPullback.hom) ≫ pullback.fst Z.hom q =
      (A.cartesian.isoPullback.hom ≫ pullback.lift (pullback.fst Y.hom q ≫ f.left)
        (pullback.snd Y.hom q) _) ≫ pullback.fst Z.hom q
    simp only [Category.assoc]
    rw [B.cartesian.isoPullback_hom_fst, A.map_left_toOriginal, pullback.lift_fst,
      A.cartesian.isoPullback_hom_fst_assoc]
  · exact (Over.w (_ ≫ _)).trans (Over.w (_ ≫ _)).symm

end Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections.Reduction
