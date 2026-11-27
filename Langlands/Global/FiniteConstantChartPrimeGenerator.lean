import Langlands.Global.FiniteConstantCurveChart
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree
import Mathlib.GroupTheory.OrderOfElement

/-! # Prime power generators on finite-constant affine curve charts -/

noncomputable section

universe u

open AlgebraicCurve IntermediateField IsDedekindDomain Polynomial
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin nonZeroDivisors
  Langlands.Global.FiniteConstantCurveChart Polynomial

namespace Langlands.Global

/-- A nonzero prime in a Dedekind domain with finite class group has a nonzero
power generator belonging to no other nonzero prime. -/
theorem exists_primePowerGenerator (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Finite (ClassGroup R)] (P : HeightOneSpectrum R) :
    ∃ d : R, d ≠ 0 ∧ d ∈ P.asIdeal ∧ ∀ Q : HeightOneSpectrum R, Q ≠ P → d ∉ Q.asIdeal := by
  let J : (Ideal R)⁰ := ⟨P.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr P.ne_bot⟩
  let n := Nat.card (ClassGroup R)
  have hn : 0 < n := Nat.card_pos
  have hpow : ClassGroup.mk0 (J ^ n) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  have hprincipal : Submodule.IsPrincipal ((J ^ n : (Ideal R)⁰) : Ideal R) :=
    (ClassGroup.mk0_eq_one_iff (J ^ n).property).mp hpow
  obtain ⟨d, hd⟩ := hprincipal.principal
  change P.asIdeal ^ n = Ideal.span ({d} : Set R) at hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_zero] at hd
    exact pow_ne_zero _ P.ne_bot hd
  have hmem : d ∈ P.asIdeal ^ n := hd ▸ Ideal.subset_span (Set.mem_singleton d)
  refine ⟨d, hd0, Ideal.pow_le_self hn.ne' hmem, fun Q hQP hdQ => ?_⟩
  have hle : P.asIdeal ^ n ≤ Q.asIdeal := hd ▸ (Ideal.span_singleton_le_iff_mem Q.asIdeal).mpr hdQ
  have hPQ : P.asIdeal ≤ Q.asIdeal := fun a ha =>
    Q.isPrime.mem_of_pow_mem n (hle (Ideal.pow_mem_pow ha n))
  exact hQP (HeightOneSpectrum.ext ((P.isMaximal.eq_of_le Q.isPrime.ne_top hPQ).symm))

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  (s : F) [FiniteDimensional k⟮s⟯ F]

/-- The normalized affine chart has finite class group for every transcendental parameter,
including when the induced extension of rational function fields is inseparable. -/
theorem finite_classGroup_normalizedCurveChart (hs : Transcendental k s) :
    Finite (ClassGroup (CurveModel.chartRing k ({s} : Set F))) := by
  classical
  let A := Algebra.adjoin k ({s} : Set F)
  let C := CurveModel.chartRing k ({s} : Set F)
  let f : k[X] →+* A := (CurveModel.aevalAdjoin k s).toRingHom
  have hsurj : Function.Surjective f := CurveModel.aevalAdjoin_surjective k s
  have hinj : Function.Injective f := fun _ _ h =>
    (transcendental_iff_injective.mp hs) (congrArg Subtype.val h)
  let : Algebra k[X] A := f.toAlgebra
  let : Algebra k[X] C := (algebraMap A C |>.comp f).toAlgebra
  let : IsScalarTower k[X] A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite k[X] A := Module.Finite.of_surjective (Algebra.linearMap k[X] A) hsurj
  let : Module.Finite A C := FiniteConstantCurveChart.moduleFinite k F s
  let : Module.Finite k[X] C := Module.Finite.trans A C
  have hAC : Function.Injective (algebraMap A C) := fun _ _ h => by
    apply Subtype.ext
    exact congrArg (fun c : C => (c : F)) h
  let : Module.IsTorsionFree k[X] C :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (hAC.comp hinj)
  let : Module.Free k[X] C := Module.free_of_finite_type_torsion_free'
  let : Algebra.IsAlgebraic k[X] C := inferInstance
  let : Fintype k := Fintype.ofFinite k
  let : Fintype (ClassGroup C) := ClassGroup.fintypeOfAdmissibleOfAlgebraic
    (Module.Free.chooseBasis k[X] C) Polynomial.cardPowDegreeIsAdmissible
  exact inferInstance

end Langlands.Global
