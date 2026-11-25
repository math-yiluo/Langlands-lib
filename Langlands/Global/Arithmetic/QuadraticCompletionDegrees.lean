import Langlands.ClassFieldTheory.Global.LocalUnitCohomology
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Langlands.Global.PrimeToFiniteAdeles
import Mathlib.FieldTheory.KummerPolynomial

/-! # Quadratic number fields with prescribed even local degrees -/

noncomputable section

open Polynomial NumberField IsDedekindDomain IntermediateField
open Langlands.ClassFieldTheory.Global
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global

open AdelicFunctoriality

universe u

variable {F : Type u} [Field F] [NumberField F]

private theorem exists_open_nonsquare_set (v : FinitePlace F) :
    ∃ U : Set (FiniteCompletion F v), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∀ y : FiniteCompletion F v, y ^ 2 ≠ x := by
  let K := FiniteCompletion F v
  obtain ⟨π, hπ⟩ := exists_unitsExponent_eq_neg_one v
  let U := Metric.ball (π : K) ‖(π : K)‖
  refine ⟨U, Metric.isOpen_ball,
    ⟨π, Metric.mem_ball_self (norm_pos_iff.mpr π.ne_zero)⟩, fun x hx y hy => ?_⟩
  have hxv : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x = Valued.v (π : K) := by
    apply Valuation.map_eq_of_sub_lt
    apply (Valued.toNormedField.norm_lt_iff).mp
    simpa only [U, Metric.mem_ball, dist_eq_norm] using hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [← hy, h, zero_pow (by decide : 2 ≠ 0), map_zero] at hxv
    exact π.ne_zero ((Valuation.zero_iff Valued.v).mp hxv.symm)
  let z : Kˣ := Units.mk0 y hy0
  have hval : Valued.v ((z ^ 2 : Kˣ) : K) = Valued.v (π : K) := by
    simpa only [Units.val_pow_eq_pow_val, z, Units.val_mk0, hy] using hxv
  have hodd := WithZero.exp_injective ((valued_units v (z ^ 2)).symm.trans
    (hval.trans (valued_units v π)))
  rw [map_pow, toAdd_pow, hπ, nsmul_eq_mul] at hodd
  omega

/-- Simultaneously choose a global nonsquare that is a nonsquare at the specified
finite places and lies within distance one of `-1` in every infinite completion. -/
theorem exists_nonsquare_near_neg_one (S : Finset (FinitePlace F)) :
    ∃ a : F, (∀ x : F, x ^ 2 ≠ a) ∧
      (∀ v ∈ S, ∀ x : FiniteCompletion F v, x ^ 2 ≠ algebraMap F (FiniteCompletion F v) a) ∧
      ∀ w : InfinitePlace F, ‖algebraMap F w.Completion a + 1‖ < 1 := by
  classical
  obtain ⟨p, _⟩ := existsUnique_finitePlace_natCast_mem 2 Nat.prime_two
  let v₀ := (placeAbove F p).val
  let T := insert v₀ S
  choose U hU hUne hs using fun v : T => exists_open_nonsquare_set v.val
  obtain ⟨a, ha, hi⟩ := AdelicFunctoriality.exists_algebraMap_mem_open T U hU hUne
    (fun w => Metric.ball (-1 : w.Completion) 1) (fun _ => Metric.isOpen_ball)
    (fun w => ⟨_, Metric.mem_ball_self zero_lt_one⟩)
  refine ⟨a, fun x hx => ?_, fun v hv => ?_, fun w => ?_⟩
  · let v : T := ⟨v₀, Finset.mem_insert_self _ _⟩
    apply hs v _ (ha v) (algebraMap F (FiniteCompletion F v₀) x)
    rw [← map_pow, hx]
  · let w : T := ⟨v, Finset.mem_insert_of_mem hv⟩
    exact hs w _ (ha w)
  · simpa only [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using hi w

private theorem two_dvd_finrank_of_root {K M : Type u} [Field K] [Field M] [Algebra K M]
    (a : K) (ha : ∀ x : K, x ^ 2 ≠ a) (b : M) (hb : b ^ 2 = algebraMap K M a) :
    2 ∣ Module.finrank K M := by
  let p : K[X] := X ^ 2 - C a
  have hp : Irreducible p := X_pow_sub_C_irreducible_of_prime Nat.prime_two ha
  have hm : p.Monic := monic_X_pow_sub_C a two_ne_zero
  have hb0 : aeval b p = 0 := by simp [p, hb]
  have he := minpoly.eq_of_irreducible_of_monic hp hb0 hm
  have hbi : IsIntegral K b := ⟨p, hm, hb0⟩
  let N := K⟮b⟯
  have hd : Module.finrank K N = 2 := by
    rw [IntermediateField.adjoin.finrank hbi, ← he, natDegree_X_pow_sub_C]
  exact hd ▸ Module.finrank_dvd_finrank_right K N M

/-- A totally complex quadratic extension with even local degree above every
selected finite place of a number field. -/
def QuadraticCompletionDegreesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F)),
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (_ : FiniteDimensional F E),
      Module.finrank F E = 2 ∧ IsTotallyComplex E ∧
      (∀ v ∈ S, ∀ (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal],
        2 ∣ Module.finrank (FiniteCompletion F v) (FiniteCompletion E w))

/-- Weak approximation realizes the prescribed quadratic local degrees. -/
theorem quadraticCompletionDegrees : QuadraticCompletionDegreesStatement.{u} := by
  intro F _ _ S
  obtain ⟨a, ha, hfin, hinf⟩ := exists_nonsquare_near_neg_one S
  let p : F[X] := X ^ 2 - C a
  let : Fact (Irreducible p) := ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_two ha⟩
  let E := AdjoinRoot p
  let b := (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero)
  let : FiniteDimensional F E := b.finite
  let : NumberField E := NumberField.of_module_finite F E
  let r : E := AdjoinRoot.root p
  have hr : r ^ 2 = algebraMap F E a := by
    have h := AdjoinRoot.eval₂_root p
    change p.eval₂ (algebraMap F E) r = 0 at h
    simpa [p, sub_eq_zero] using h
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [b.finrank]
    exact natDegree_X_pow_sub_C
  · refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp fun hw => ?_⟩
    let v := w.comap (algebraMap F E)
    let e := InfinitePlace.Completion.extensionEmbedding v
    have h : ‖v.embedding (a + 1)‖ < 1 := by
      have hv := hinf v
      rw [← map_one (algebraMap F v.Completion), ← map_add] at hv
      rwa [← extensionEmbedding_algebraMap v,
        (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero e)]
    have h' : ‖w.embedding (algebraMap F E (a + 1))‖ < 1 := by
      rw [w.norm_embedding_eq]
      rwa [v.norm_embedding_eq] at h
    rw [← InfinitePlace.embedding_of_isReal_apply hw, Complex.norm_real, map_add, map_one,
      ← hr] at h'
    simp only [map_add, map_pow, map_one, Real.norm_eq_abs] at h'
    rw [abs_of_nonneg (by positivity)] at h'
    linarith [sq_nonneg (w.embedding_of_isReal hw r)]
  · intro v hv w _
    let K := FiniteCompletion F v
    let M := FiniteCompletion E w
    let x := algebraMap E M r
    have hx : x ^ 2 = algebraMap K M (algebraMap F K a) := by
      rw [show x ^ 2 = algebraMap E M (r ^ 2) from (map_pow _ _ _).symm, hr]
      exact (IsScalarTower.algebraMap_apply F E M a).symm.trans
        (IsScalarTower.algebraMap_apply F K M a)
    exact two_dvd_finrank_of_root _ (hfin v hv) x hx

end Langlands.Global
