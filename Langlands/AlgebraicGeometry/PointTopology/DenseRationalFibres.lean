import Langlands.AlgebraicGeometry.AffineRationalDetection
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformEtaleChartInjectivityProof
import Langlands.AlgebraicGeometry.PointTopology.DenseRationalFamily
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Equality of morphisms detected on rational fibres -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [Field K]

private theorem coordinate_productMap_surjective
    (T X : Over (Spec (CommRingCat.of K))) [IsAffine T.left] [IsAffine X.left]
    [IsAffine (T ⊗ X).left] : Function.Surjective
      (Algebra.TensorProduct.productMap (affineCoordinatePullback K (snd T X))
        (affineCoordinatePullback K (fst T X))) := by
  let Φ := Algebra.TensorProduct.productMap (affineCoordinatePullback K (snd T X))
    (affineCoordinatePullback K (fst T X))
  let Φr : AffineCoordinateRing K X ⊗[K] AffineCoordinateRing K T →+*
      Γ((T ⊗ X).left, ⊤) := Φ.toRingHom
  have hle : Subring.closure (Set.range (fst T X).left.appTop ∪ Set.range (snd T X).left.appTop) ≤
      Φr.range := by
    rw [Subring.closure_le]
    apply Set.union_subset
    · rintro _ ⟨z, rfl⟩
      let a : AffineCoordinateRing K T := z
      refine ⟨1 ⊗ₜ a, ?_⟩
      change Φ (1 ⊗ₜ a) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
      rfl
    · rintro _ ⟨z, rfl⟩
      let a : AffineCoordinateRing K X := z
      refine ⟨a ⊗ₜ 1, ?_⟩
      change Φ (a ⊗ₜ 1) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
      rfl
  intro s
  apply hle
  rw [Over.fst_left, Over.snd_left,
    Langlands.AlgebraicGeometry.AlgebraicSpace.closure_range_pullback_appTop_eq_top]
  trivial

/-- On a product with two affine factors over a field, a dense family of rational
fibres of the second factor detects equality of maps into a separated target.
The first factor may be nonreduced. -/
private theorem hom_ext_of_denseRationalFibres_affine {J : Type v}
    {T X Y : Over (Spec (CommRingCat.of K))} [IsAffine T.left] [IsAffine X.left]
    [IsReduced X.left] [IsSeparated Y.hom] (p : J → RationalPoint K X)
    (hp : HasDenseRationalPointFamily p) {f g : T ⊗ X ⟶ Y}
    (h : ∀ i, lift (𝟙 T) (toUnit T ≫ p i) ≫ f = lift (𝟙 T) (toUnit T ≫ p i) ≫ g) :
    f = g := by
  have : IsAffine (T ⊗ X).left := inferInstanceAs (IsAffine (pullback T.hom X.hom))
  have : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  let eK := (affineCoordinateAlgEquiv K (ringTestSelfIso K)).trans (spectrumCoordinateAlgEquiv K K)
  let e (i : J) : AffineCoordinateRing K X →ₐ[K] K :=
    eK.toAlgHom.comp (affineCoordinatePullback K (p i))
  have he (a : AffineCoordinateRing K X) (ha : ∀ i, e i a = 0) : a = 0 := by
    let s : Γ(X.left, ⊤) := a
    change s = 0
    apply eq_zero_of_basicOpen_eq_bot (s := s)
    apply eq_bot_iff.mpr
    intro x hx
    change Dense (⋃ i : J, Set.range (p i).left) at hp
    obtain ⟨z, hz, hz'⟩ := hp.inter_open_nonempty _ (X.left.basicOpen s).isOpen ⟨x, hx⟩
    obtain ⟨i, w, rfl⟩ := Set.mem_iUnion.mp hz'
    have hi : (p i).left.appTop s = 0 :=
      eK.injective ((ha i).trans (map_zero eK).symm)
    change w ∈ (p i).left ⁻¹ᵁ (X.left.basicOpen s) at hz
    rw [Scheme.preimage_basicOpen_top, hi, Scheme.basicOpen_zero] at hz
    exact (TopologicalSpace.Opens.mem_bot.mp hz).elim
  let uT : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) := toUnit T
  have hunit (a : AffineCoordinateRing K (Over.mk (𝟙 (Spec (CommRingCat.of K))))) :
      affineCoordinatePullback K uT a = algebraMap K (AffineCoordinateRing K T) (eK a) := by
    have ha : algebraMap K _ (eK a) = a := eK.injective (by simp)
    calc
      _ = affineCoordinatePullback K uT (algebraMap K _ (eK a)) :=
        congrArg (affineCoordinatePullback K uT) ha.symm
      _ = _ := (affineCoordinatePullback K uT).commutes _
  let Φ := Algebra.TensorProduct.productMap (affineCoordinatePullback K (snd T X))
    (affineCoordinatePullback K (fst T X))
  let r (i : J) : T ⟶ T ⊗ X := lift (𝟙 T) (toUnit T ≫ p i)
  have hΦ (i : J) : (affineCoordinatePullback K (r i)).comp Φ =
      Algebra.TensorProduct.productMap ((Algebra.ofId K _).comp (e i)) (AlgHom.id K _) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro a b
    change (affineCoordinatePullback K (r i)).comp Φ (a ⊗ₜ b) =
      Algebra.TensorProduct.productMap ((Algebra.ofId K _).comp (e i)) (AlgHom.id K _) (a ⊗ₜ b)
    rw [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul, map_mul]
    congr 1
    · rw [← AlgHom.comp_apply, ← affineCoordinatePullback_comp]
      simp only [r, lift_snd]
      change affineCoordinatePullback K (uT ≫ p i) a = _
      rw [affineCoordinatePullback_comp, AlgHom.comp_apply, hunit]
      rfl
    · rw [← AlgHom.comp_apply, ← affineCoordinatePullback_comp]
      simp [r, affineCoordinatePullback_id]
  let j := equalizer.ι f g
  have : IsIso j.left := IsClosedImmersion.isIso_of_injective_of_isAffine (f := j.left) (by
    rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨z, rfl⟩ := coordinate_productMap_surjective T X s
    have hz : ∀ i, Algebra.TensorProduct.productMap ((Algebra.ofId K _).comp (e i))
        (AlgHom.id K _) z = 0 := by
      intro i
      let l := equalizer.lift (r i) (h i)
      have hl : l.left ≫ j.left = (r i).left := by
        rw [← Over.comp_left, equalizer.lift_ι]
      let s : Γ((T ⊗ X).left, ⊤) := Φ z
      rw [← hΦ i, AlgHom.comp_apply, affineCoordinatePullback_apply]
      change (r i).left.appTop s = 0
      rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      change j.left.appTop s = 0 at hs
      rw [hs, map_zero]
    change Φ z = 0
    simp only [Langlands.AlgebraicGeometry.tensorEvaluations_separate e he z hz, map_zero])
  apply Over.OverMorphism.ext
  apply (cancel_epi j.left).mp
  exact congrArg (fun a ↦ a.left) (equalizer.condition f g)

/-- A dense family in a reduced factor detects equality on a product with an
affine parameter, even when the parameter is nonreduced. -/
abbrev DenseRationalFibresStatement : Prop :=
  ∀ {K : Type u} [Field K] {J : Type v}
    {T X Y : Over (Spec (CommRingCat.of K))} [IsAffine T.left]
    [IsReduced X.left] [IsSeparated Y.hom]
    (p : J → RationalPoint K X), HasDenseRationalPointFamily p →
    ∀ {f g : T ⊗ X ⟶ Y},
      (∀ i, lift (𝟙 T) (toUnit T ≫ p i) ≫ f = lift (𝟙 T) (toUnit T ≫ p i) ≫ g) → f = g

set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict to an affine cover of the reduced factor and lift the rational
points that lie in each chart. The affine comparison applies on every chart. -/
theorem hom_ext_of_denseRationalFibres : DenseRationalFibresStatement.{u, v} := by
  intro K _ J T X Y _ _ _ p hp f g h
  let C := X.left.affineOpenCover
  let D := C.openCover.pullback₁ (snd T X).left
  apply Over.OverMorphism.ext
  apply D.hom_ext
  intro k
  let i : C.I₀ := k
  let j := C.f i
  let V := Over.mk (j ≫ X.hom)
  let a : V ⟶ X := Over.homMk j rfl
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (C.f i))
  have : IsAffine V.left := inferInstanceAs (IsAffine (Spec (C.X i)))
  have : IsReduced V.left := isReduced_of_isOpenImmersion j
  let I := {k : J // Set.range (p k).left ⊆ Set.range j}
  let q (k : I) : RationalPoint K V :=
    Over.homMk (IsOpenImmersion.lift j (p k.1).left k.2) (by
      change IsOpenImmersion.lift j (p k.1).left k.2 ≫ j ≫ X.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w (p k.1)])
  have hq (k : I) : q k ≫ a = p k.1 :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hd : HasDenseRationalPointFamily q := by
    change Dense (⋃ k : I, Set.range (q k).left)
    change Dense (⋃ k : J, Set.range (p k).left) at hp
    refine (hp.preimage j.isOpenEmbedding.isOpenMap).mono ?_
    intro v hv
    change j v ∈ ⋃ k : J, Set.range (p k).left at hv
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp hv
    have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of K)))).left :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
    have hk : Set.range (p k).left ⊆ Set.range j := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w z, hz]
      exact Set.mem_range_self v
    refine Set.mem_iUnion.mpr ⟨⟨k, hk⟩, z, j.isOpenEmbedding.injective ?_⟩
    have hleft := congrArg (fun m ↦ m.left) (hq ⟨k, hk⟩)
    change (q ⟨k, hk⟩).left ≫ j = (p k).left at hleft
    rw [← Scheme.Hom.comp_apply, hleft, hz]
  have he : (T ◁ a) ≫ f = (T ◁ a) ≫ g := by
    apply hom_ext_of_denseRationalFibres_affine q hd
    intro k
    have hk : lift (𝟙 T) (toUnit T ≫ q k) ≫ (T ◁ a) =
        lift (𝟙 T) (toUnit T ≫ p k.1) := by
      rw [lift_whiskerLeft, Category.assoc, hq]
    simp only [← Category.assoc, hk]
    exact h k.1
  have hPb : IsPullback (pullback.snd T.hom V.hom) (T ◁ a).left a.left
      (pullback.snd T.hom X.hom) := by
    apply IsPullback.of_bot (t := (IsPullback.of_hasPullback T.hom X.hom).flip)
    · simpa only [Over.whiskerLeft_left_fst, Over.w] using
        (IsPullback.of_hasPullback T.hom V.hom).flip
    · exact (Over.whiskerLeft_left_snd a).symm
  change pullback.fst (pullback.snd T.hom X.hom) a.left ≫ f.left =
    pullback.fst (pullback.snd T.hom X.hom) a.left ≫ g.left
  rw [← cancel_epi hPb.flip.isoPullback.hom, hPb.flip.isoPullback_hom_fst_assoc,
    hPb.flip.isoPullback_hom_fst_assoc]
  exact congrArg (fun m ↦ m.left) he

end Langlands.AlgebraicGeometry.PointTopology
