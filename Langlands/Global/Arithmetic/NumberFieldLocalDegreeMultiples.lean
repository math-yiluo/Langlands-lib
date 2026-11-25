import Langlands.ClassFieldTheory.Global.LocalUnitCohomology
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Langlands.Global.PrimeToFiniteAdeles
import Mathlib.FieldTheory.KummerExtension

/-! # Number-field extensions with prescribed local degree multiples -/

noncomputable section

open Polynomial NumberField IsDedekindDomain IntermediateField
open Langlands.ClassFieldTheory.Global
open scoped NumberField WithZero Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global

open AdelicFunctoriality

universe u v

variable {F : Type u} [Field F] [NumberField F]

private theorem exists_element_with_uniformizerValues (S : Finset (FinitePlace F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ v ∈ S,
      (Valued.v (algebraMap F (FiniteCompletion F v) a) : ℤᵐ⁰) = WithZero.exp (-1) := by
  classical
  by_cases hS : S.Nonempty
  · choose π hπ using fun v : S => exists_unitsExponent_eq_neg_one v.val
    let U (v : S) : Set (FiniteCompletion F v.val) :=
      Metric.ball (π v) ‖(π v : FiniteCompletion F v.val)‖
    obtain ⟨a, ha, _⟩ := exists_algebraMap_mem_open S U
      (fun _ => Metric.isOpen_ball)
      (fun v => ⟨π v, Metric.mem_ball_self (norm_pos_iff.mpr (π v).ne_zero)⟩)
      (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.univ_nonempty)
    have hav (v : S) : (Valued.v (algebraMap F (FiniteCompletion F v.val) a) : ℤᵐ⁰) =
        WithZero.exp (-1) := by
      calc
        _ = Valued.v (π v : FiniteCompletion F v.val) := by
          apply Valuation.map_eq_of_sub_lt
          apply (Valued.toNormedField.norm_lt_iff).mp
          simpa only [U, Metric.mem_ball, dist_eq_norm] using ha v
        _ = _ := by rw [valued_units, hπ v]
    refine ⟨a, ?_, fun v hv => hav ⟨v, hv⟩⟩
    intro h
    obtain ⟨v, hv⟩ := hS
    have hval := hav ⟨v, hv⟩
    simp only [h, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  · exact ⟨1, one_ne_zero, fun v hv => (hS ⟨v, hv⟩).elim⟩

private theorem localDegree_dvd_of_power_eq {L : Type v} [Field L] [NumberField L] [Algebra F L]
    (v : FinitePlace F) (w : FinitePlace L) [w.asIdeal.LiesOver v.asIdeal]
    {n : ℕ} (hn : 0 < n) {a : F} (ha₀ : a ≠ 0)
    (ha : (Valued.v (algebraMap F (FiniteCompletion F v) a) : ℤᵐ⁰) = WithZero.exp (-1))
    {b : L} (hb : b ^ n = algebraMap F L a) :
    n ∣ Module.finrank (FiniteCompletion F v) (FiniteCompletion L w) := by
  let x := algebraMap L (FiniteCompletion L w) b
  have hx : x ^ n = FiniteExtension.completionMap v w (algebraMap F (FiniteCompletion F v) a) := by
    change (algebraMap L (FiniteCompletion L w) b) ^ n = _
    rw [← map_pow, hb, FiniteExtension.completionMap_coe]
  have hb₀ : b ≠ 0 := by
    intro h
    apply ha₀
    apply (algebraMap F L).injective
    simpa only [h, zero_pow hn.ne', map_zero] using hb.symm
  let y := Units.mk0 x ((_root_.map_ne_zero (algebraMap L (FiniteCompletion L w))).2 hb₀)
  let t := Multiplicative.toAdd (unitsExponent w y)
  let e := w.asIdeal.ramificationIdx (𝓞 F)
  have hval : WithZero.exp (n • t) = WithZero.exp (e • (-1 : ℤ)) := calc
    _ = (Valued.v (x ^ n) : ℤᵐ⁰) := by
      rw [WithZero.exp_nsmul, map_pow]
      exact congrArg (fun z : ℤᵐ⁰ => z ^ n) (valued_units w y).symm
    _ = _ := by rw [hx, FiniteExtension.valuation_completionMap, ha, WithZero.exp_nsmul]
  have hcount := WithZero.exp_injective hval
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_neg_one] at hcount
  have hdiv : n ∣ e := Int.natCast_dvd_natCast.mp
    ⟨-t, by simpa only [mul_neg, neg_neg] using congrArg Neg.neg hcount.symm⟩
  rw [localDegree_eq]
  exact hdiv.trans (dvd_mul_right _ _)

/-- A finite Galois extension with local degrees divisible by the requested integer
at every upper place over the specified finite set. -/
def NumberFieldLocalDegreeMultiplesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F)) (n : ℕ), 0 < n →
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (_ : IsGalois F L),
      ∀ v ∈ S, ∀ (w : FinitePlace L) [w.asIdeal.LiesOver v.asIdeal],
        n ∣ Module.finrank (FiniteCompletion F v) (FiniteCompletion L w)

/-- The splitting field of a binomial with a uniformizer value at each selected place
has the required local degree multiples. -/
theorem numberFieldLocalDegreeMultiples : NumberFieldLocalDegreeMultiplesStatement.{u} := by
  intro F _ _ S n hn
  obtain ⟨a, ha₀, ha⟩ := exists_element_with_uniformizerValues S
  let f : F[X] := X ^ n - C a
  let L := f.SplittingField
  let : NumberField L := NumberField.of_module_finite F L
  let : IsGalois F L := IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C a (Nat.cast_ne_zero.mpr hn.ne') ha₀)
  let : NeZero n := ⟨hn.ne'⟩
  let b := rootOfSplitsXPowSubC hn a L
  have hb : b ^ n = algebraMap F L a := rootOfSplitsXPowSubC_pow a L
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    fun v hv w _ => localDegree_dvd_of_power_eq v w hn ha₀ (ha v hv) hb⟩

/-- The subfield generated by one root has global degree `n` and local degree `n`
above the prescribed finite places. -/
theorem exists_numberFieldExtension_exactLocalDegree
    (S : Finset (FinitePlace F)) {n : ℕ} (hn : 0 < n) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
      Module.finrank F L = n ∧
      ∀ v ∈ S, ∀ (w : FinitePlace L) [w.asIdeal.LiesOver v.asIdeal],
        Module.finrank (FiniteCompletion F v) (FiniteCompletion L w) = n := by
  classical
  obtain ⟨p, _⟩ := existsUnique_finitePlace_natCast_mem 2 Nat.prime_two
  let v₀ := (placeAbove F p).val
  let T := insert v₀ S
  obtain ⟨a, ha₀, ha⟩ := exists_element_with_uniformizerValues T
  let f : F[X] := X ^ n - C a
  let M := f.SplittingField
  let : NeZero n := ⟨hn.ne'⟩
  let b := rootOfSplitsXPowSubC hn a M
  have hb : b ^ n = algebraMap F M a := rootOfSplitsXPowSubC_pow a M
  let L := F⟮b⟯
  let c : L := ⟨b, mem_adjoin_simple_self F b⟩
  have hc : c ^ n = algebraMap F L a := Subtype.ext hb
  let : NumberField L := NumberField.of_module_finite F L
  have hglobal : Module.finrank F L ≤ n := by
    rw [show Module.finrank F L = (minpoly F b).natDegree from
      IntermediateField.adjoin.finrank (IsIntegral.of_finite F b),
      ← natDegree_X_pow_sub_C (n := n) (r := a)]
    have hf : aeval b f = 0 := by simp [f, hb]
    exact natDegree_le_of_dvd (minpoly.dvd F b hf) (monic_X_pow_sub_C a hn.ne').ne_zero
  have hlocal_le (v : FinitePlace F) (w : FinitePlace L) [hw : w.asIdeal.LiesOver v.asIdeal] :
      Module.finrank (FiniteCompletion F v) (FiniteCompletion L w) ≤ Module.finrank F L :=
    (Finset.single_le_sum
      (f := fun r : FinitePlacesAbove L v =>
        Module.finrank (FiniteCompletion F v) (FiniteCompletion L r.val))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨w, hw⟩)).trans
      (finiteLocalDegree_sum_le (L := L) v)
  have hlocal (v : FinitePlace F) (hv : v ∈ T) (w : FinitePlace L) [w.asIdeal.LiesOver v.asIdeal] :
      Module.finrank (FiniteCompletion F v) (FiniteCompletion L w) = n :=
    le_antisymm ((hlocal_le v w).trans hglobal)
      (Nat.le_of_dvd Module.finrank_pos (localDegree_dvd_of_power_eq v w hn ha₀ (ha v hv) hc))
  let w₀ := placeAbove L v₀
  refine ⟨L, inferInstance, inferInstance, inferInstance, le_antisymm hglobal ?_, ?_⟩
  · rw [← hlocal v₀ (Finset.mem_insert_self _ _) w₀.val]
    exact hlocal_le v₀ w₀.val
  · exact fun v hv w _ => hlocal v (Finset.mem_insert_of_mem hv) w

end Langlands.Global
