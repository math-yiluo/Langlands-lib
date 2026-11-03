import Langlands.AlgebraicGeometry.AffineGenericUnitRestriction

/-! # Compatible scalar units on actual affine generic opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (q : Y ⟶ X) (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {U V : X.Opens}

/-- A nonzero base scalar as a unit on the actual generic inverse image
of an affine total open. -/
def affineGenericScalarUnit (hU : IsAffineOpen U) (r : R) (hr : r ≠ 0) :
    Γ(Y, q ⁻¹ᵁ U)ˣ := by
  let := affineSectionAlgebra p hU
  let := pullbackSectionAlgebra q U
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, U) R⁰) Γ(Y, q ⁻¹ᵁ U) :=
    isLocalization_pullbackSectionAlgebra q U K p s H hU
  exact (IsLocalization.map_units (M := Algebra.algebraMapSubmonoid Γ(X, U) R⁰)
    Γ(Y, q ⁻¹ᵁ U) ⟨algebraMap R Γ(X, U) r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩).unit

@[simp]
theorem affineGenericScalarUnit_val (hU : IsAffineOpen U) (r : R) (hr : r ≠ 0) :
    letI := affineSectionAlgebra p hU
    (affineGenericScalarUnit p K q s H hU r hr : Γ(Y, q ⁻¹ᵁ U)) =
      q.app U (algebraMap R Γ(X, U) r) := by
  exact IsUnit.unit_spec _

/-- The scalar units are compatible with actual affine-open restriction. -/
theorem affineGenericScalarUnit_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) (r : R) (hr : r ≠ 0) :
    Units.map (Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op).hom.toMonoidHom
      (affineGenericScalarUnit p K q s H hU r hr) =
        affineGenericScalarUnit p K q s H hV r hr := by
  let := affineSectionAlgebra p hU
  let := affineSectionAlgebra p hV
  apply Units.ext
  simp only [Units.coe_map, affineGenericScalarUnit_val]
  change Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op
    (q.app U (algebraMap R Γ(X, U) r)) =
      q.app V (algebraMap R Γ(X, V) r)
  have hf := (affineSectionRestrictionAlgHom p hU hV hVU).commutes r
  change X.presheaf.map (homOfLE hVU).op (algebraMap R Γ(X, U) r) =
    algebraMap R Γ(X, V) r at hf
  rw [← hf]
  simp only [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- A ratio of nonzero base scalars, as an actual generic unit. -/
def affineGenericScalarRatio (hU : IsAffineOpen U) (r d : R)
    (hr : r ≠ 0) (hd : d ≠ 0) : Γ(Y, q ⁻¹ᵁ U)ˣ :=
  affineGenericScalarUnit p K q s H hU d hd *
    (affineGenericScalarUnit p K q s H hU r hr)⁻¹

@[simp]
theorem affineGenericScalarRatio_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) (r d : R) (hr : r ≠ 0) (hd : d ≠ 0) :
    Units.map (Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op).hom.toMonoidHom
      (affineGenericScalarRatio p K q s H hU r d hr hd) =
        affineGenericScalarRatio p K q s H hV r d hr hd := by
  simp only [affineGenericScalarRatio, map_mul, map_inv,
    affineGenericScalarUnit_restrict p K q s H hU hV hVU r hr,
    affineGenericScalarUnit_restrict p K q s H hU hV hVU d hd]

variable [ValuationRing R]

/-- Scalar-times-unit data for an actual generic unit on an affine open
meeting the closed fibre, with projectivity retained as an input. -/
def affineGenericUnitDecomposition [Smooth p] [GeometricallyConnected p]
    (hU : IsAffineOpen U)
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty)
    (hproj : letI := affineSectionAlgebra p hU; Module.Projective R Γ(X, U))
    (b : Γ(Y, q ⁻¹ᵁ U)ˣ) :
    letI := affineSectionAlgebra p hU
    letI := pullbackSectionAlgebra q U
    Langlands.CommutativeAlgebra.ScalarUnitDecomposition R Γ(X, U) Γ(Y, q ⁻¹ᵁ U) b := by
  let := affineSectionAlgebra p hU
  let := pullbackSectionAlgebra q U
  let : Module.Projective R Γ(X, U) := hproj
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, U) R⁰) Γ(Y, q ⁻¹ᵁ U) :=
    isLocalization_pullbackSectionAlgebra q U K p s H hU
  exact Langlands.CommutativeAlgebra.scalarUnitDecompositionOfProjective
    (closedFibreIdeal_isPrime_affineSectionAlgebra p hU hmeet) b

/-- The chosen decomposition is an exact identity of units under the
original generic section map. -/
theorem affineGenericUnitDecomposition_eq [Smooth p] [GeometricallyConnected p]
    (hU : IsAffineOpen U)
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty)
    (hproj : letI := affineSectionAlgebra p hU; Module.Projective R Γ(X, U))
    (b : Γ(Y, q ⁻¹ᵁ U)ˣ) :
    letI := affineSectionAlgebra p hU
    letI := pullbackSectionAlgebra q U
    let n := affineGenericUnitDecomposition p K q s H hU hmeet hproj b
    b = affineGenericScalarRatio p K q s H hU n.denominator n.numerator
      n.denominator_ne_zero n.numerator_ne_zero *
        Units.map (q.app U).hom.toMonoidHom n.totalUnit := by
  let := affineSectionAlgebra p hU
  let := pullbackSectionAlgebra q U
  let n := affineGenericUnitDecomposition p K q s H hU hmeet hproj b
  change b = affineGenericScalarRatio p K q s H hU n.denominator n.numerator
    n.denominator_ne_zero n.numerator_ne_zero *
      Units.map (q.app U).hom.toMonoidHom n.totalUnit
  let D := affineGenericScalarUnit p K q s H hU n.denominator n.denominator_ne_zero
  let N := affineGenericScalarUnit p K q s H hU n.numerator n.numerator_ne_zero
  let a := Units.map (q.app U).hom.toMonoidHom n.totalUnit
  apply mul_left_cancel (a := D)
  change D * b = D * (N * D⁻¹ * a)
  have hcancel : D * (N * D⁻¹ * a) = N * a := by
    calc
      D * (N * D⁻¹ * a) = (D * D⁻¹) * (N * a) := by ac_rfl
      _ = N * a := by rw [mul_inv_cancel, one_mul]
  rw [hcancel]
  apply Units.ext
  have hn := n.cleared_eq
  change (q.app U).hom (algebraMap R Γ(X, U) n.denominator) * (b : Γ(Y, q ⁻¹ᵁ U)) =
    (q.app U).hom (algebraMap R Γ(X, U) n.numerator) *
      (q.app U).hom (n.totalUnit : Γ(X, U)) at hn
  simp only [D, N, a, Units.val_mul, Units.coe_map,
    affineGenericScalarUnit_val]
  change (q.app U).hom (algebraMap R Γ(X, U) n.denominator) * (b : Γ(Y, q ⁻¹ᵁ U)) =
    (q.app U).hom (algebraMap R Γ(X, U) n.numerator) *
      (q.app U).hom (n.totalUnit : Γ(X, U))
  exact hn

end Langlands.AlgebraicGeometry
