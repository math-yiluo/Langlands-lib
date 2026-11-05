import Langlands.Global.CurvePlaceCompletionExtension
import Langlands.Global.CurvePlaceCompletionResidue
import Langlands.LocalField.DVRDegreeProof

/-! # Actual completed valuation rings in curve-place extensions -/

noncomputable section

universe u

open IsDedekindDomain
open scoped Valued WithZero Langlands.Global.CurvePlaceCompletionExtension
open WithZeroTopology

namespace Langlands.Global.CurvePlaceCompletedIntegersExtension

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  (p : AlgebraicCurve.Place k K) (q : CurvePlacesAbove k L p)

open CurvePlaceCompletionExtension

/-- The original completion embedding preserves and reflects the completed valuation rings. -/
theorem completionMap_mem_integers_iff (x : curvePlaceCompletion p) :
    completionMap p q x ∈ curvePlaceCompletionIntegers q.1 ↔
      x ∈ curvePlaceCompletionIntegers p := by
  refine (p.heightOneSpectrum.denseRange_algebraMap K).induction_on x ?_ ?_
  · have hp : IsClopen {a : curvePlaceCompletion p |
        a ∈ curvePlaceCompletionIntegers p} :=
      Valued.isClopen_valuationSubring (curvePlaceCompletion p)
    have hq : IsClopen {a : curvePlaceCompletion p |
        completionMap p q a ∈ curvePlaceCompletionIntegers q.1} :=
      (Valued.isClopen_valuationSubring (curvePlaceCompletion q.1)).preimage
      (continuous_completionMap p q)
    have hc := (Homeomorph.refl (curvePlaceCompletion p)).isClosed_setOfPred_iff hp hq
    simpa only [Homeomorph.refl_apply, id_eq, iff_comm] using hc
  · intro a
    rw [completionMap_algebraMap, curvePlaceCompletion_mem_integers_iff,
      curvePlaceCompletion_mem_integers_iff, CurvePlaceCompletionExtension.mem_iff]

/-- Restrict the original completion embedding to the actual completed integer rings. -/
def completionIntegersMap :
    curvePlaceCompletionIntegers p →+* curvePlaceCompletionIntegers q.1 :=
  (completionMap p q).restrict (curvePlaceCompletionIntegers p).toSubring
    (curvePlaceCompletionIntegers q.1).toSubring
    (fun x hx => (completionMap_mem_integers_iff p q x).mpr hx)

@[simp]
theorem completionIntegersMap_coe (x : curvePlaceCompletionIntegers p) :
    (completionIntegersMap p q x : curvePlaceCompletion q.1) = completionMap p q x := rfl

theorem continuous_completionIntegersMap : Continuous (completionIntegersMap p q) :=
  ((continuous_completionMap p q).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem completionIntegersMap_original (x : p.toValuationSubring) :
    completionIntegersMap p q (curvePlaceIntegersMap p x) =
      curvePlaceIntegersMap q.1 (integersMap p q x) := by
  apply Subtype.ext
  exact completionMap_algebraMap p q x

scoped instance (priority := 50) :
    Algebra (curvePlaceCompletionIntegers p) (curvePlaceCompletion q.1) :=
  ((completionMap p q).comp (curvePlaceCompletionIntegers p).subtype).toAlgebra

scoped instance (priority := 50) :
    Algebra (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1) :=
  (completionIntegersMap p q).toAlgebra

scoped instance : IsScalarTower (curvePlaceCompletionIntegers p)
    (curvePlaceCompletion p) (curvePlaceCompletion q.1) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (curvePlaceCompletionIntegers p)
    (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1) :=
  .of_algebraMap_eq fun _ => rfl

/-- The maximal ideals restrict exactly along the constructed integral map. -/
theorem completionIntegersMap_mem_maximalIdeal_iff (x : curvePlaceCompletionIntegers p) :
    completionIntegersMap p q x ∈ IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers q.1) ↔
      x ∈ IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers p) := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  change completionMap p q (x : curvePlaceCompletion p) = 0 ∨
    (completionMap p q (x : curvePlaceCompletion p))⁻¹ ∉ curvePlaceCompletionIntegers q.1 ↔
      (x : curvePlaceCompletion p) = 0 ∨ (x : curvePlaceCompletion p)⁻¹ ∉ curvePlaceCompletionIntegers p
  rw [map_eq_zero, ← map_inv₀, completionMap_mem_integers_iff]

scoped instance : IsLocalHom (algebraMap (curvePlaceCompletionIntegers p)
    (curvePlaceCompletionIntegers q.1)) where
  map_nonunit x hx := by
    by_contra hn
    exact ((completionIntegersMap_mem_maximalIdeal_iff p q x).mpr hn) hx

scoped instance : Module.IsTorsionFree (curvePlaceCompletionIntegers p)
    (curvePlaceCompletionIntegers q.1) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr fun _x _y h =>
    Subtype.ext ((completionMap p q).injective (congrArg Subtype.val h))

/-- The original valuation-ring embedding is a local homomorphism. -/
scoped instance originalLocalHom :
    IsLocalHom (algebraMap p.toValuationSubring q.1.toValuationSubring) where
  map_nonunit x hx := by
    by_contra hn
    have hm := (Ideal.mem_of_liesOver q.1.heightOneSpectrum.asIdeal
      p.heightOneSpectrum.asIdeal x).mp hn
    exact hm hx

/-- The canonical original and completed residue comparisons commute with extension. -/
theorem completionResidueEquiv_algebraMap (x : p.ResidueField) :
    curvePlaceCompletionResidueEquiv q.1
        (algebraMap p.ResidueField q.1.ResidueField x) =
      algebraMap (IsLocalRing.ResidueField (curvePlaceCompletionIntegers p))
          (IsLocalRing.ResidueField (curvePlaceCompletionIntegers q.1))
        (curvePlaceCompletionResidueEquiv p x) := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [IsLocalRing.ResidueField.algebraMap_residue,
    curvePlaceCompletionResidueEquiv_residue,
    curvePlaceCompletionResidueEquiv_residue,
    IsLocalRing.ResidueField.algebraMap_residue]
  exact congrArg (IsLocalRing.residue _)
    (completionIntegersMap_original p q a).symm

/-- Inertia degree is unchanged by passing to the actual completions. -/
theorem completionIntegers_inertiaDeg :
    (IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers q.1)).inertiaDeg
        (curvePlaceCompletionIntegers p) =
      q.1.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers p))
    (IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers q.1)),
    Ideal.inertiaDeg_eq_of_isMaximal
      p.heightOneSpectrum.asIdeal q.1.heightOneSpectrum.asIdeal]
  apply Eq.symm
  apply Algebra.finrank_eq_of_equiv_equiv
    (curvePlaceCompletionResidueEquiv p) (curvePlaceCompletionResidueEquiv q.1)
  ext x
  exact (completionResidueEquiv_algebraMap p q x).symm

/-- The original ramification exponent determines the completed valuation map. -/
theorem valuation_completionMap (x : curvePlaceCompletion p) :
    (Valued.v (completionMap p q x) : ℤᵐ⁰) =
      Valued.v x ^ q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring := by
  have hp := Valued.continuous_valuation_of_surjective
    (p.heightOneSpectrum.valuedAdicCompletion_surjective K)
  have hq := Valued.continuous_valuation_of_surjective
    (q.1.heightOneSpectrum.valuedAdicCompletion_surjective L)
  refine congrFun ((p.heightOneSpectrum.denseRange_algebraMap K).equalizer
    (hq.comp (continuous_completionMap p q)) (hp.pow _) ?_) x
  funext a
  change Valued.v (completionMap p q (algebraMap K (curvePlaceCompletion p) a)) =
    Valued.v (algebraMap K (curvePlaceCompletion p) a) ^
      q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring
  rw [completionMap_algebraMap]
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  rw [← HeightOneSpectrum.valuation_liesOver L p.heightOneSpectrum q.1.heightOneSpectrum,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ p.heightOneSpectrum.ne_bot]

/-- The adic valuation on the completed integer ring has its original normalization. -/
theorem completionIntegers_intValuation (x : curvePlaceCompletionIntegers p) :
    (IsDiscreteValuationRing.maximalIdeal (curvePlaceCompletionIntegers p)).intValuation x =
      (Valued.v (x : curvePlaceCompletion p) : ℤᵐ⁰) := by
  let R := curvePlaceCompletionIntegers p
  let m := IsDiscreteValuationRing.maximalIdeal R
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, a, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hπv : Valued.v (π : curvePlaceCompletion p) = WithZero.exp (-1) := by
    have h := Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (Valued.v : Valuation (curvePlaceCompletion p) ℤᵐ⁰)) hπ.maximalIdeal_eq
    exact h.trans (congrArg (fun a : ℤᵐ⁰ˣ => (a : ℤᵐ⁰))
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (p.heightOneSpectrum.valuedAdicCompletion_surjective K)))
  have hπm : m.intValuation π = WithZero.exp (-1) :=
    m.intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
  have ha : m.intValuation (a : R) = 1 := by
    simp [m, IsDiscreteValuationRing.maximalIdeal]
  have hav : Valued.v ((a : R) : curvePlaceCompletion p) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp a.isUnit
  change m.intValuation ((a : R) * π ^ n) =
    Valued.v (((a : R) : curvePlaceCompletion p) * (π : curvePlaceCompletion p) ^ n)
  rw [map_mul, map_pow, map_mul, map_pow, ha, hav, hπv, hπm]

/-- Ramification index is unchanged by passing to the actual completions. -/
theorem completionIntegers_ramificationIdx :
    (IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers q.1)).ramificationIdx
        (curvePlaceCompletionIntegers p) =
      q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring := by
  let m := IsDiscreteValuationRing.maximalIdeal (curvePlaceCompletionIntegers p)
  let n := IsDiscreteValuationRing.maximalIdeal (curvePlaceCompletionIntegers q.1)
  have : n.asIdeal.LiesOver m.asIdeal :=
    inferInstanceAs ((IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers q.1)).LiesOver
      (IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers p)))
  obtain ⟨π, hπ⟩ := m.intValuation_exists_uniformizer
  have h := HeightOneSpectrum.intValuation_liesOver m n π
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ m.ne_bot] at h
  change m.intValuation π ^
      (IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers q.1)).ramificationIdx
        (curvePlaceCompletionIntegers p) = n.intValuation (completionIntegersMap p q π) at h
  rw [hπ, completionIntegers_intValuation q.1, completionIntegersMap_coe,
    valuation_completionMap, ← completionIntegers_intValuation p, hπ] at h
  exact pow_right_injective₀ (by simp) (by simp [← WithZero.exp_zero]) h

variable [FiniteDimensional K L]

/-- The original ramification-inertia product is bounded by the completed field degree. -/
theorem localDegree_lowerBound :
    q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring *
        q.1.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring ≤
      Module.finrank (curvePlaceCompletion p) (curvePlaceCompletion q.1) := by
  have h := Langlands.LocalField.dvrDegreeLowerBound
    (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1)
    (curvePlaceCompletion p) (curvePlaceCompletion q.1)
  rwa [completionIntegers_ramificationIdx p q, completionIntegers_inertiaDeg p q] at h

end Langlands.Global.CurvePlaceCompletedIntegersExtension
