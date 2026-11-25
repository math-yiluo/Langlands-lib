/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison

set_option linter.privateModule false

/-!
# Finite-level bounded constructibility for proper support

Source: Stacks Project, Tags 0GL0, 095U and 0GL6; current blueprint,
sec-six-functors-basics/sk-prop-sf-cbc/prop-finite-compact-support-constructibility
(blueprint: theorem-results-from-etale-theory--3).

We use intrinsic finite-torsion constructibility and the recorded compactification
candidate. The scalar comparison is the adjunct of compact support of the tensor unit,
followed by the recorded, normalized restriction-of-scalars comparison. In particular
it is the canonical B-linear map, not an unspecified isomorphism of underlying objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

private theorem finite_homology_support_iff
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
    · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi
  · rintro ⟨a, b, _, h⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun hia ↦ hi (h i (Or.inl hia))),
      le_of_not_gt (fun hbi ↦ hi (h i (Or.inr hbi)))⟩

private theorem coefficient_has_invertible_exponent
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀)) (n : ℕ) (_hn : 1 ≤ n) :
    HasInvertibleExponent (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      (Spec (.of K₀)) := by
  let v := Padic.coefficientExtensionAbsoluteValue l E
  have hv := spectralNorm_extends (K := Padic l) (L := E)
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).2
    change v (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E) l]
    change spectralNorm (Padic l) E ((algebraMap (Padic l) E) (l : Padic l)) < 1
    rw [hv]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hkill : (l ^ n : Padic.coefficientExtensionRing l E n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hm n
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · apply ULift.ext
    change ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0
    simpa only [Nat.cast_pow] using hkill
  · have hu := (hl.pow n).map (Scheme.ΓSpecIso (.of K₀)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hu

end AlgebraicGeometry.Scheme
