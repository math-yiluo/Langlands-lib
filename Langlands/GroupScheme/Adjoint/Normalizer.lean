import Langlands.GroupScheme.Adjoint.SplitTorus
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Actual normalizer points under the adjoint split-torus image -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsAdjointSplitTorusImage

variable {k : Type u} [Field k]
variable {G A : GroupScheme (Spec (CommRingCat.of k))}
variable {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
variable {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
variable (h : IsAdjointSplitTorusImage q i j p)

include h

private theorem conjugate_range_le {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : T ≅ T} (hn : IsNormalizingPoint i n σ) :
    SubgroupFunctor.range (j ≫ (A.innerIso (n ≫ q.hom.hom)).hom) ≤
      SubgroupFunctor.range j := by
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Flat (CommGroupScheme.groupHom p).hom.hom.left := h.flat
  let : Surjective (CommGroupScheme.groupHom p).hom.hom.left := h.surjective
  let : LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left :=
    h.locallyOfFinitePresentation
  have hsquare :
      CommGroupScheme.groupHom p ≫ j ≫ (A.innerIso (n ≫ q.hom.hom)).hom =
        CommGroupScheme.groupHom σ.hom ≫ CommGroupScheme.groupHom p ≫ j := by
    calc
      _ = i ≫ q ≫ (A.innerIso (n ≫ q.hom.hom)).hom := by
        rw [← Category.assoc, h.comp_eq, Category.assoc]
      _ = i ≫ (G.innerIso n).hom ≫ q := by rw [innerIso_hom_comp]
      _ = CommGroupScheme.groupHom σ.hom ≫ i ≫ q := by
        rw [← Category.assoc, hn, Category.assoc]
      _ = _ := by rw [← h.comp_eq]
  rintro U x ⟨y, rfl⟩
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst y.left (CommGroupScheme.groupHom p).hom.hom.left ≫ U.hom)
  let a : V ⟶ U :=
    Over.homMk (pullback.fst y.left (CommGroupScheme.groupHom p).hom.hom.left) rfl
  let z : V ⟶ T.toGrp.X :=
    Over.homMk (pullback.snd y.left (CommGroupScheme.groupHom p).hom.hom.left) (by
      rw [← Over.w (CommGroupScheme.groupHom p).hom.hom, ← Category.assoc,
        ← pullback.condition, Category.assoc, Over.w y]
      rfl)
  have haz : a ≫ y = z ≫ (CommGroupScheme.groupHom p).hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range j a
  refine SubgroupFunctor.mem_range.mpr
    ⟨z ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫
      (CommGroupScheme.groupHom p).hom.hom, ?_⟩
  change (z ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫
      (CommGroupScheme.groupHom p).hom.hom) ≫ j.hom.hom =
    a ≫ (y ≫ (j ≫ (A.innerIso (n ≫ q.hom.hom)).hom).hom.hom)
  have hs := congrArg (fun f : T.toGrp ⟶ A => f.hom.hom) hsquare
  simp only [Grp.comp_hom_hom] at hs ⊢
  rw [← Category.assoc a y, haz]
  simpa only [Category.assoc] using congrArg (fun f => z ≫ f) hs.symm

private def normalizerEnd (n : normalizerPoints i) : T_ad.toGrp ⟶ T_ad.toGrp :=
  letI : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  (show (SubgroupFunctor.range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩).factorHom
    (j ≫ (A.innerIso (n.val ≫ q.hom.hom)).hom)
    (h.conjugate_range_le (isNormalizingPoint_normalizingAut i n))

private theorem normalizerEnd_comp (n : normalizerPoints i) :
    h.normalizerEnd n ≫ j = j ≫ (A.innerIso (n.val ≫ q.hom.hom)).hom := by
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

private theorem normalizerEnd_inv (n : normalizerPoints i) :
    h.normalizerEnd n ≫ h.normalizerEnd n⁻¹ = 𝟙 T_ad.toGrp := by
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (show (SubgroupFunctor.range j).IsRepresentedBy j from
    ⟨inferInstance, rfl⟩).hom_ext
  rw [Category.assoc, h.normalizerEnd_comp, ← Category.assoc,
    h.normalizerEnd_comp, Category.assoc, Category.id_comp]
  change j ≫ (A.innerIso (n.val ≫ q.hom.hom)).hom ≫
    (A.innerIso (n.val⁻¹ ≫ q.hom.hom)).hom = j
  rw [GrpObj.inv_comp, innerIso_inv_hom, Iso.hom_inv_id, Category.comp_id]

/-- Conjugation by the actual image of a source normalizer point restricts
to an automorphism of the actual adjoint split torus. -/
def normalizerAut (n : normalizerPoints i) : T_ad ≅ T_ad where
  hom := Additive.ofMul (h.normalizerEnd n)
  inv := Additive.ofMul (h.normalizerEnd n⁻¹)
  hom_inv_id := congrArg Additive.ofMul (h.normalizerEnd_inv n)
  inv_hom_id := by
    have hi := h.normalizerEnd_inv n⁻¹
    rw [inv_inv] at hi
    exact congrArg Additive.ofMul hi

/-- The constructed torus automorphism is the restriction of actual conjugation. -/
theorem isNormalizingPoint_normalizerAut (n : normalizerPoints i) :
    IsNormalizingPoint j (n.val ≫ q.hom.hom) (h.normalizerAut n) :=
  (h.normalizerEnd_comp n).symm

/-- The adjoint quotient restricts to a homomorphism of actual normalizer point groups. -/
def normalizerPointsMap : normalizerPoints i →* normalizerPoints j where
  toFun n := ⟨n.val ≫ q.hom.hom, ⟨h.normalizerAut n, h.isNormalizingPoint_normalizerAut n⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' n m := Subtype.ext (MonObj.mul_comp n.val m.val _)

@[simp] theorem normalizerPointsMap_apply (n : normalizerPoints i) :
    (h.normalizerPointsMap n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) =
      n.val ≫ q.hom.hom := rfl

/-- The actual source and image normalizer automorphisms commute with the actual torus map. -/
theorem normalizingAut_comp (n : normalizerPoints i) :
    (normalizingAut i n).hom ≫ p =
      p ≫ (normalizingAut j (h.normalizerPointsMap n)).hom := by
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have ht := isNormalizingPoint_normalizingAut j (h.normalizerPointsMap n)
  change j ≫ (A.innerIso (n.val ≫ q.hom.hom)).hom =
    CommGroupScheme.groupHom (normalizingAut j (h.normalizerPointsMap n)).hom ≫ j at ht
  have he :
      CommGroupScheme.groupHom ((normalizingAut i n).hom ≫ p) ≫ j =
        CommGroupScheme.groupHom (p ≫ (normalizingAut j (h.normalizerPointsMap n)).hom) ≫ j := by
    calc
      _ = (CommGroupScheme.groupHom (normalizingAut i n).hom ≫ i) ≫ q := by
        change (CommGroupScheme.groupHom (normalizingAut i n).hom ≫
          CommGroupScheme.groupHom p) ≫ j = _
        rw [Category.assoc, h.comp_eq, Category.assoc]
      _ = (i ≫ (G.innerIso n.val).hom) ≫ q := by
        rw [isNormalizingPoint_normalizingAut i n]
      _ = (CommGroupScheme.groupHom p ≫ j) ≫
          (A.innerIso (n.val ≫ q.hom.hom)).hom := by
        rw [Category.assoc, innerIso_hom_comp, ← Category.assoc, ← h.comp_eq]
      _ = _ := by
        rw [Category.assoc, ht]
        rfl
  have hf := (show (SubgroupFunctor.range j).IsRepresentedBy j from
    ⟨inferInstance, rfl⟩).hom_ext he
  exact congrArg Additive.ofMul hf

end Langlands.GroupScheme.IsAdjointSplitTorusImage
