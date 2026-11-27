import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.BaseChange.DistinguishedPairEulerComparison
import Langlands.BaseChange.FinitePairFactorNonvanishing
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Global.Factors.TemperedPoleRegions
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Comparing actual finite pair factors at the distinguished completion -/

noncomputable section

set_option autoImplicit false

universe u uQ uI

namespace Langlands.BaseChange

open Automorphic Global RankinSelberg LocalFactor LocalFactor.Archimedean _root_.Polynomial
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison RelativeWeilEngine
open scoped BigOperators NumberField

local notation "Γ(" blocks ")" =>
  (fun z : ℂ => (LocalFactor.ReciprocalEntire.denominator (gammaProduct blocks) z)⁻¹)

private theorem gammaValue_prod {I : Type*} (X : Finset I) (A : I → List GammaBlock) :
    (fun z => ∏ i ∈ X, Γ(A i) z) = Γ(X.toList.flatMap A) := by
  have happ (B C : List GammaBlock) (z : ℂ) :
      Γ(B ++ C) z = Γ(B) z * Γ(C) z := by
    simp [gammaProduct, LocalFactor.ReciprocalEntire.denominator_product, mul_comm]
  funext z
  rw [← Finset.prod_map_toList]
  induction X.toList with
  | nil => simp [gammaProduct, LocalFactor.ReciprocalEntire.denominator_product]
  | cons i is ih => simp [happ, ih]

private theorem spectralPoint_pow_residueBase (q f : ℕ) (z : ℂ) :
    spectralPoint (q ^ f) z = spectralPoint q z ^ f := by
  simp only [spectralPoint, Nat.cast_pow, ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]

private theorem clear_distinguished_products {I J : Type*} [DecidableEq I]
    (under : J → I) (fiber : I → Finset J) (hfiber : ∀ w v, w ∈ fiber v ↔ under w = v)
    (v₀ : I) (w₀ : J) (hw₀ : fiber v₀ = {w₀}) (l : I → ℂ) (l' : J → ℂ)
    (a b p p' : ℂ) (hL : HasProd l p) (hp : p ≠ 0) (hL' : HasProd l' p') (hp' : p' ≠ 0)
    (ha : l v₀ = a⁻¹) (hb : l' w₀ = b⁻¹)
    (haway : ∀ v ≠ v₀, l v = ∏ w ∈ fiber v, l' w) : a * p = b * p' := by
  have ha₀ : a ≠ 0 := by
    intro hz
    exact ne_zero_of_hasProd hL hp v₀ (by simp [ha, hz])
  have hb₀ : b ≠ 0 := by
    intro hz
    exact ne_zero_of_hasProd hL' hp' w₀ (by simp [hb, hz])
  have hF := (hasProd_pi_single v₀ a).mul hL
  have hE := (hasProd_pi_single v₀ b).mul (hasProd_fiberwise under fiber hfiber hL')
  refine hF.unique (hE.congr_fun fun v => ?_)
  by_cases hv : v = v₀
  · subst v
    simp [hw₀, ha, hb, ha₀, hb₀]
  · simp [Pi.mulSingle, Function.update_of_ne hv, haway v hv]

/-- Away-place comparison of the finite forward and dual Euler values and
open-unit-disk nonvanishing at the unique distinguished completions identify
their normalized forward polynomials in the lower residue variable. -/
def CompletedPairDistinguishedPolynomialComparisonStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (r t : ℕ) (I : Type uI) [Fintype I],
    ∀ (v₀ : FinitePlace K) (w₀ : FinitePlace L) (f : ℕ),
      placesAbove L v₀ = {w₀} → residueCardinality w₀ = residueCardinality v₀ ^ f →
    ∀ (T Td : I → CuspidalOperatorRealization K r) (T' Td' : I → CuspidalOperatorRealization K t)
      (U Ud : CuspidalOperatorRealization L r) (U' Ud' : CuspidalOperatorRealization L t)
      (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
      (P' : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T' i))
      (Pd : ∀ i, CuspidalSpectralPresentation.{u, uQ} (Td i))
      (Pd' : ∀ i, CuspidalSpectralPresentation.{u, uQ} (Td' i))
      (Q : CuspidalSpectralPresentation.{u, uQ} U) (Q' : CuspidalSpectralPresentation.{u, uQ} U')
      (Qd : CuspidalSpectralPresentation.{u, uQ} Ud) (Qd' : CuspidalSpectralPresentation.{u, uQ} Ud')
      (hP : ∀ i, HasIrreducibleAdmissibleComponents (P i))
      (hP' : ∀ i, HasIrreducibleAdmissibleComponents (P' i))
      (hPd : ∀ i, HasIrreducibleAdmissibleComponents (Pd i))
      (hPd' : ∀ i, HasIrreducibleAdmissibleComponents (Pd' i))
      (hQ : HasIrreducibleAdmissibleComponents Q) (hQ' : HasIrreducibleAdmissibleComponents Q')
      (hQd : HasIrreducibleAdmissibleComponents Qd) (hQd' : HasIrreducibleAdmissibleComponents Qd')
      (cF : ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K) (P i) (P' i) (Pd i) (Pd' i)
        (hP i) (hP' i) (hPd i) (hPd' i))
      (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L) Q Q' Qd Qd' hQ hQ' hQd hQd')
      (SF : I → Finset (FinitePlace K)) (SE : Finset (FinitePlace L))
      (AF AdF : I → List GammaBlock) (AE AdE : List GammaBlock) (εF : I → ℂˣ) (εE : ℂˣ),
      (∀ i v, v ∉ SF i → (cF i).epsilon v = (1, 0)) →
      (∀ i, HasGlobalEquation (cF i).finiteL (cF i).finiteDualL (cF i).finiteEpsilon
        Γ(AF i) Γ(AdF i) (fun _ => (εF i : ℂ)) (SF i)) →
      HasGlobalEquation cE.finiteL cE.finiteDualL cE.finiteEpsilon Γ(AE) Γ(AdE)
        (fun _ => (εE : ℂ)) SE →
      (∀ v ≠ v₀, ∀ z, (∏ i, (cF i).finiteL v z) = ∏ w ∈ placesAbove L v, cE.finiteL w z) →
      (∀ v ≠ v₀, ∀ z, (∏ i, (cF i).finiteDualL v z) = ∏ w ∈ placesAbove L v, cE.finiteDualL w z) →
      (∀ i z, ‖z‖ < 1 → ((cF i).lPolynomial v₀).eval z ≠ 0 ∧ ((cF i).dualLPolynomial v₀).eval z ≠ 0) →
      (∀ z, ‖z‖ < 1 → (cE.lPolynomial w₀).eval z ≠ 0 ∧ (cE.dualLPolynomial w₀).eval z ≠ 0) →
      (cE.lPolynomial w₀).comp (X ^ f) = ∏ i, (cF i).lPolynomial v₀

set_option maxHeartbeats 1900000 in
/-- Combine the lower equations, remove the distinguished Euler factors in the
product limits, and compare their denominators by their root orders. -/
theorem completedPairDistinguishedPolynomialComparison :
    CompletedPairDistinguishedPolynomialComparisonStatement.{u,uQ,uI} := by
  classical
  intro K L _ _ _ _ _ _ _ r t I _ v₀ w₀ f hw hq T Td T' Td' U Ud U' Ud' P P' Pd Pd' Q Q' Qd Qd'
    hP hP' hPd hPd' hQ hQ' hQd hQd' cF cE SF SE AF AdF AE AdE εF εE hSF hF hE haway hdaway hpF hpE
  let S := Finset.univ.biUnion SF
  let q := residueCardinality v₀
  have hqF (v : FinitePlace K) := FinitePairFactorChoice.one_lt_residueCardinality v
  have hqE (w : FinitePlace L) := FinitePairFactorChoice.one_lt_residueCardinality w
  have hf : 0 < f := Nat.pos_of_ne_zero fun hz => (hqE w₀).ne' (by simpa [hz] using hq)
  have hsub (i : I) : SF i ⊆ S := fun _ h => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩
  have hF' (i : I) := (hF i).changeSet (T' := S)
    (fun v hv hn => False.elim (hn (hsub i hv)))
    (fun v _ hn z => by simp [FinitePairFactorChoice.finiteEpsilon, hSF i v hn])
  have hcombined := hasGlobalEquation_finsetProd Finset.univ (fun i _ => hF' i)
  rw [gammaValue_prod, gammaValue_prod] at hcombined
  let PF := ∏ i, (cF i).lPolynomial v₀
  let PdF := ∏ i, (cF i).dualLPolynomial v₀
  let PE := (cE.lPolynomial w₀).comp (X ^ f)
  let PdE := (cE.dualLPolynomial w₀).comp (X ^ f)
  have hPF : PF.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    exact Finset.prod_eq_one fun i _ => by
      rw [← coeff_zero_eq_eval_zero]
      exact ((cF i).lPolynomial_spec v₀).coeff_zero
  have hPE : PE.coeff 0 = 1 := by
    simpa only [PE, coeff_zero_eq_eval_zero, eval_comp, eval_pow, eval_X, zero_pow hf.ne'] using
      (cE.lPolynomial_spec w₀).coeff_zero
  have hsepF := Global.GLPoleRegion.hasNoReflectedCommonZero_of_poleFree (hqF v₀)
    (P := PF) (Pd := PdF)
    (fun x hx => by
      rw [eval_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => (hpF i x hx).1)
    (fun x hx => by
      rw [eval_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => (hpF i x hx).2)
  have hxpow {x : ℂ} (hx : ‖x‖ < 1) : ‖x ^ f‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx hf.ne'
  have hsepE := Global.GLPoleRegion.hasNoReflectedCommonZero_of_poleFree (hqF v₀)
    (P := PE) (Pd := PdE)
    (fun x hx => by simpa only [PE, eval_comp, eval_pow, eval_X] using (hpE (x ^ f) (hxpow hx)).1)
    (fun x hx => by simpa only [PdE, eval_comp, eval_pow, eval_X] using (hpE (x ^ f) (hxpow hx)).2)
  symm
  refine distinguishedPairEulerFromEquations (FinitePlace K) (FinitePlace L) S SE _ _ _ _ _ _
    (Finset.univ.toList.flatMap AF) (Finset.univ.toList.flatMap AdF) AE AdE
    (fun _ => ∏ i, (εF i : ℂ)) (fun _ => (εE : ℂ)) q PF PdF PE PdE
    (hqF v₀) hPF hPE hcombined hE ?_ ?_ ?_ ?_ ?_
  · intro z
    have hpos (v : FinitePlace K) : 0 < (residueCardinality v : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans (hqF v)
    constructor
    · exact analyticAt_const.mul (S.analyticAt_fun_prod fun v _ => Finset.univ.analyticAt_fun_prod
        fun i _ => epsilonMonomial_analyticAt (residueCardinality v) (hpos v) _ _ z)
    · exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (εF i).ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun v _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
          epsilonMonomial_ne_zero (residueCardinality v) (hpos v) _ _ z)
  · intro z
    have hpos (w : FinitePlace L) : 0 < (residueCardinality w : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans (hqE w)
    exact ⟨analyticAt_const.mul (SE.analyticAt_fun_prod fun w _ =>
      epsilonMonomial_analyticAt (residueCardinality w) (hpos w) _ _ z),
      mul_ne_zero εE.ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ =>
        epsilonMonomial_ne_zero (residueCardinality w) (hpos w) _ _ z)⟩
  · obtain ⟨σF, Lf, Ld, -, -, hprodF, -⟩ := hcombined
    obtain ⟨σE, Uf, Ud, -, -, hprodE, -⟩ := hE
    refine ⟨max σF σE, fun z hz => ?_⟩
    obtain ⟨⟨hp, hp₀⟩, hpd, hpd₀⟩ := hprodF z ((le_max_left _ _).trans_lt hz)
    obtain ⟨⟨hr, hr₀⟩, hrd, hrd₀⟩ := hprodE z ((le_max_right _ _).trans_lt hz)
    refine ⟨Lf z, Ld z, Uf z, Ud z, hp, hr, hpd, hrd, ?_, ?_⟩
    · refine clear_distinguished_products (fun w : FinitePlace L => w.under (𝓞 K)) (placesAbove L)
        mem_placesAbove v₀ w₀ hw _ _ _ _ _ _ hp hp₀ hr hr₀ ?_ ?_ (fun v hv => haway v hv z)
      · simp only [PF, FinitePairFactorChoice.finiteL, eval_prod, Finset.prod_inv_distrib, q]
      · simp only [PE, FinitePairFactorChoice.finiteL, eval_comp, eval_pow, eval_X, hq,
          spectralPoint_pow_residueBase, q]
    · refine clear_distinguished_products (fun w : FinitePlace L => w.under (𝓞 K)) (placesAbove L)
        mem_placesAbove v₀ w₀ hw _ _ _ _ _ _ hpd hpd₀ hrd hrd₀ ?_ ?_ (fun v hv => hdaway v hv z)
      · simp only [PdF, FinitePairFactorChoice.finiteDualL, eval_prod, Finset.prod_inv_distrib, q]
      · simp only [PdE, FinitePairFactorChoice.finiteDualL, eval_comp, eval_pow, eval_X, hq,
          spectralPoint_pow_residueBase, q]
  · intro x hx hroot hdual
    exact hsepF x hx ⟨hroot, by simpa only [div_eq_mul_inv] using hdual⟩
  · intro x hx hroot hdual
    exact hsepE x hx ⟨hroot, by simpa only [div_eq_mul_inv] using hdual⟩

end Langlands.BaseChange
