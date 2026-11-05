import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.HopfPrimitiveQuotient

/-! # Product decomposition along one step of a split series

If `K ⟶ H ⟶ V` is one step of a split series of an affine group over `Spec R`, the quotient
map has a section preserving the unit, and `(κ, t) ↦ j(κ) · s(t)` identifies `K ⊗ V` with `H`
as schemes over `Spec R`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitSeriesDecomposition

open RelativeRoot

section Category

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {K H V : C} [GrpObj H] [GrpObj V]

/-- A section of a group homomorphism can be normalized to preserve the unit. -/
theorem exists_unit_section (q : H ⟶ V) [IsMonHom q] (s : V ⟶ H) (hs : s ≫ q = 𝟙 V) :
    ∃ s' : V ⟶ H, s' ≫ q = 𝟙 V ∧ η[V] ≫ s' = η[H] := by
  refine ⟨s * (toUnit V ≫ η[V] ≫ s)⁻¹, ?_, ?_⟩
  · rw [MonObj.mul_comp, GrpObj.inv_comp, hs, Category.assoc, Category.assoc, hs,
      Category.comp_id, ← Hom.one_def, inv_one, mul_one]
  · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc η[V] (toUnit V),
      toUnit_unique (η[V] ≫ toUnit V) (𝟙 _), Category.id_comp, mul_inv_cancel, Hom.one_def,
      toUnit_unit, Category.id_comp]

/-- A homomorphism `q : H ⟶ V` of group objects with kernel `j` and a section `s`: the map
`(κ, t) ↦ j(κ) · s(t)` is an isomorphism `K ⊗ V ≅ H`. -/
theorem isIso_mul_of_section (j : K ⟶ H) [Mono j] (q : H ⟶ V) [IsMonHom q]
    (hjq : j ≫ q = 1) (s : V ⟶ H) (hs : s ≫ q = 𝟙 V)
    (hlift : ∀ x : H ⟶ H, x ≫ q = 1 → ∃ y : H ⟶ K, y ≫ j = x) :
    IsIso ((fst K V ≫ j) * (snd K V ≫ s)) := by
  obtain ⟨r, hr⟩ := hlift (𝟙 H * (q ≫ s)⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hs, Category.comp_id, Category.id_comp,
      mul_inv_cancel])
  have h2 : ((fst K V ≫ j) * (snd K V ≫ s)) ≫ q = snd K V := by
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hjq, hs, MonObj.comp_one, one_mul,
      Category.comp_id]
  have h1 : ((fst K V ≫ j) * (snd K V ≫ s)) ≫ r = fst K V := by
    rw [← cancel_mono j, Category.assoc, hr, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv,
      ← Category.assoc _ q, h2, mul_inv_cancel_right]
  refine ⟨lift r q, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h1, Category.id_comp]
    · rw [Category.assoc, lift_snd, h2, Category.id_comp]
  · rw [MonObj.comp_mul, ← Category.assoc, lift_fst, hr, ← Category.assoc, lift_snd,
      inv_mul_cancel_right]

end Category

variable {R : CommRingCat.{u}}

/-- One step `K ⟶ H ⟶ V` of a split series of an affine group: the quotient map has a section
`s` preserving the unit, and `(κ, t) ↦ j(κ) · s(t)` is an isomorphism `K ⊗ V ≅ H` of schemes
over `Spec R`. -/
theorem exists_section_isIso_mul {K H V : GroupScheme (Spec R)} (j : K ⟶ H) (q : H ⟶ V)
    (hj : IsClosedSubgroup j) (hq : IsFppfQuotient (SubgroupFunctor.range j) q)
    (hV : IsVectorGroupOfDimension V 1) {n : ℕ} (hK : HasSplitSeries n K)
    [IsAffineHom H.X.hom] :
    ∃ s : V.X ⟶ H.X, s ≫ q.hom.hom = 𝟙 V.X ∧ η[V.X] ≫ s = η[H.X] ∧
      IsIso ((fst K.X V.X ≫ j.hom.hom) * (snd K.X V.X ≫ s)) := by
  obtain ⟨hflat, hsurj, hlfp, hjq⟩ := hq
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom K.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hKv := SplitUnipotentAffineTorsor.cocyclesVanish_of_hasSplitSeries
    (fun _ hV' T _ U _ _ _ ξ => Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV' T U ξ)
    n K hK this
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffineHom V.X.hom := hV.isAffineHom_overRing
  have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  have : Flat q.hom.hom.left := hflat
  have : Surjective q.hom.hom.left := hsurj
  have : LocallyOfFinitePresentation q.hom.hom.left := hlfp
  obtain ⟨σ, hσ⟩ := SplitUnipotentAffineTorsor.exists_section j q hjq hKv
  obtain ⟨s, hs, hηs⟩ := exists_unit_section q.hom.hom σ hσ
  refine ⟨s, hs, hηs, isIso_mul_of_section j.hom.hom q.hom.hom ?_ s hs
    (fun x hx => SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hjq x hx)⟩
  have h := SplitUnipotentAffineTorsor.comp_comp_eq_one hjq (𝟙 K.X)
  rwa [Category.id_comp] at h

/-- The scheme underlying an affine group with a split series of positive length is the
product of the next group of the series with a one-dimensional vector group. -/
theorem HasSplitSeries.exists_iso_tensor {H : GroupScheme (Spec R)} {n : ℕ}
    (h : HasSplitSeries (n + 1) H) [IsAffineHom H.X.hom] :
    ∃ (K V : GroupScheme (Spec R)) (_ : K.X ⊗ V.X ≅ H.X), HasSplitSeries n K ∧
      IsVectorGroupOfDimension V 1 ∧ IsAffineHom K.X.hom := by
  obtain ⟨K, V, j, q, hj, -, -, -, hq, hV, hK⟩ := h
  obtain ⟨s, -, -, hiso⟩ := exists_section_isIso_mul j q hj hq hV hK
  have : IsClosedImmersion j.hom.hom.left := hj
  refine ⟨K, V, asIso ((fst K.X V.X ≫ j.hom.hom) * (snd K.X V.X ≫ s)), hK, hV, ?_⟩
  rw [← Over.w j.hom.hom]
  infer_instance

end Langlands.GroupScheme.SplitSeriesDecomposition
