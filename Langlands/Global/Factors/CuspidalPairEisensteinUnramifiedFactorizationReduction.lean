import Langlands.Global.RankinSelberg.EqualEulerLocalSum
import Langlands.Global.Factors.CuspidalPairEisensteinOneplaceIntegrand
import Langlands.Global.Factors.CuspidalPairEisensteinUnramifiedFactorizationStatement
import Langlands.Automorphic.ContragredientSphericalSpectrum

/-! # The unramified factorization from the local open-cell sum

The local value `Shahidi.UnramifiedOpenCellSumStatement` of the two-block open-cell sum
implies `CuspidalPairEisensteinUnramifiedFactorizationStatement`: the open-cell integral
times the partial Euler product `L^S(1 + s, π × π')` is the partial open-cell integral over the
matrices integral outside `S`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairEisenstein.Oneplace

open MeasureTheory NumberField Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight OpenCellExhaustion CuspidalPairBoundaryNonvanishing
  CuspidalPairFunctionalEquation
open scoped CategoryTheory.MonObj

theorem map_ofTuple {n : ℕ} (z : Fin n → ℂˣ) (f : ℂˣ → ℂˣ) :
    (Unramified.Eigenvalues.ofTuple z).map f = Unramified.Eigenvalues.ofTuple (fun i => f (z i)) := by
  apply Sym.ext
  simp [Unramified.Eigenvalues.ofTuple, List.map_ofFn, Function.comp_def]

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}

/-- With Satake tuples `a` of `P` and `c` of the contragredient presentation `Pd`, the inverse of
the local pair Euler factor is `∏_(i,j) (1 - a_i c_j⁻¹ q_v^(-w))`. -/
theorem partialEulerFactor_inv_eq {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} (dualRealization T'))
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S)
    (hcontra : (dualRealization T').realization.IsContragredientOf T'.realization)
    (v : {v : FinitePlace F // v ∉ S}) (a : Fin (r + 1) → ℂˣ)
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h)))
    (c : Fin (t + 1) → ℂˣ)
    (hc : Unramified.Eigenvalues.ofTuple c =
      Pd.spectralSystem.eigenvalues v.1 (fun h => v.2 (hPd h)))
    (w : ℂ) :
    P'.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP' h)) =
        Unramified.Eigenvalues.ofTuple (fun j => (c j)⁻¹) ∧
      (partialEulerFactor P P' hP hP' v w)⁻¹ =
        ∏ i, ∏ j, (1 - (a i : ℂ) * ((c j : ℂ))⁻¹ * (residueCardinality v.1 : ℂ) ^ (-w)) := by
  have hb : P'.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP' h)) =
      Unramified.Eigenvalues.ofTuple (fun j => (c j)⁻¹) := by
    have h := CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf T'
      (dualRealization T') P' Pd hcontra v.1 (fun h => v.2 (hP' h)) (fun h => v.2 (hPd h))
    rw [← map_ofTuple, hc, h, Sym.map_map]
    simp
  refine ⟨hb, ?_⟩
  rw [partialEulerFactor, inv_inv, ← ha, hb, pairEulerPolynomial_ofTuple]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, RankinSelberg.spectralPoint,
    Units.val_inv_eq_inv_val]

omit [CompactSpace (AdeleQuotient F)] in
/-- `‖α β q_v^(-(1+s))‖ < 1` when `‖α‖ ≤ q_v^A`, `‖β‖ ≤ q_v^B` and `A + B < Re s`. -/
theorem norm_lt_one_of_bounds (v : FinitePlace F) {A B : ℝ} {α β : ℂ}
    (hα : ‖α‖ ≤ (residueCardinality v : ℝ) ^ A) (hβ : ‖β‖ ≤ (residueCardinality v : ℝ) ^ B)
    {s : ℂ} (hs : A + B < s.re) :
    ‖α * β * (residueCardinality v : ℂ) ^ (-(1 + s))‖ < 1 := by
  have hq : (1 : ℝ) < (residueCardinality v : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two
      (CuspidalPairEulerConvergence.two_le_residueCardinality v)
  have hq0 : (0 : ℝ) < (residueCardinality v : ℝ) := by linarith
  have hn : ‖(residueCardinality v : ℂ) ^ (-(1 + s))‖ =
      (residueCardinality v : ℝ) ^ (-(1 + s).re) :=
    CuspidalPairEulerConvergence.norm_spectralPoint v (1 + s)
  rw [norm_mul, norm_mul, hn]
  calc ‖α‖ * ‖β‖ * (residueCardinality v : ℝ) ^ (-(1 + s).re)
      ≤ (residueCardinality v : ℝ) ^ A * (residueCardinality v : ℝ) ^ B *
          (residueCardinality v : ℝ) ^ (-(1 + s).re) := by
        gcongr
    _ = (residueCardinality v : ℝ) ^ (A + B - (1 + s.re)) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, Complex.add_re, Complex.one_re]
        congr 1
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

omit [CompactSpace (AdeleQuotient F)] in
/-- The product `∏_(i,j) (1 - a_i c_j⁻¹ q_v^(-(1+s)))` does not vanish when the parameters are
bounded by `q_v^A` and `q_v^B` and `A + B < Re s`. -/
theorem prod_ne_zero_of_bounds (v : FinitePlace F) {A B : ℝ} (a : Fin (r + 1) → ℂˣ)
    (c : Fin (t + 1) → ℂˣ) (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ A)
    (hc : ∀ j, ‖((c j : ℂ))⁻¹‖ ≤ (residueCardinality v : ℝ) ^ B) {s : ℂ}
    (hs : A + B < s.re) :
    ∏ i, ∏ j, (1 - (a i : ℂ) * ((c j : ℂ))⁻¹ * (residueCardinality v : ℂ) ^ (-(1 + s))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  have h := norm_lt_one_of_bounds v (ha i) (hc j) hs
  intro h0
  rw [sub_eq_zero] at h0
  rw [← h0, norm_one] at h
  exact lt_irrefl _ h

omit [CompactSpace (AdeleQuotient F)] in
theorem openCellHaar_isAddLeftInvariant :
    letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
    (openCellHaar F r t).IsAddLeftInvariant := by
  let : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  have : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩
  have : LocallyCompactSpace (Adeles F) := adeles_locallyCompactSpace F
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → Adeles F))
  unfold openCellHaar
  infer_instance

end Langlands.Global.CuspidalPairEisenstein.Oneplace

namespace Langlands.Global

open MeasureTheory NumberField CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation
  CuspidalPairEisenstein CuspidalPairEisenstein.Oneplace CuspidalPairEisenstein.OpenCellExhaustion
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open RankinSelbergGlobal (partialEulerProduct)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The local value of the two-block open-cell sum implies the unramified factorization of the
open-cell integral. -/
def CuspidalPairEisensteinUnramifiedFactorizationReductionStatement : Prop :=
  Shahidi.UnramifiedOpenCellSumStatement.{u} →
    CuspidalPairEisensteinUnramifiedFactorizationStatement.{u, uQ}

set_option maxHeartbeats 1600000 in
open RankinSelbergGlobal ClassFieldTheory.Global.RelativeWeilGroup in
/-- Proof of `CuspidalPairEisensteinUnramifiedFactorizationReductionStatement`. -/
theorem cuspidalPairEisensteinUnramifiedFactorizationReduction :
    CuspidalPairEisensteinUnramifiedFactorizationReductionStatement.{u, uQ} := by
  intro hA F _ _ _ r t T T' _hT _hT' P P' Pd S hP hP' hPd ψ hψF hS φ hφ hsph
  classical
  obtain ⟨A₀, hA₀⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨B₀, hB₀⟩ := exists_hasSatakeBound_presentation T' P'
  obtain ⟨σA, hσA⟩ := hA r t A₀ B₀
  obtain ⟨σE, hσE⟩ := exists_partialEulerFactor_convergence P P' hP hP'
  have hcontra : (dualRealization T').realization.IsContragredientOf T'.realization :=
    (Automorphic.cuspidalContragredientExistence F t T').choose_spec
  refine ⟨max σA (max (σE - 1) (A₀ + B₀)), fun s hs hint => ?_⟩
  have hsA : σA < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsE : σE < (1 + s).re := by
    have h := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hsAB : A₀ + B₀ < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  obtain ⟨hsumL, hprodL⟩ := hσE (1 + s) hsE
  -- the local data at a place outside `S`
  have hdata : ∀ v : {v : FinitePlace F // v ∉ S}, ∃ (a : Fin (r + 1) → ℂˣ)
      (c : Fin (t + 1) → ℂˣ),
      Unramified.Eigenvalues.ofTuple a = P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h)) ∧
      Unramified.Eigenvalues.ofTuple c =
        Pd.spectralSystem.eigenvalues v.1 (fun h => v.2 (hPd h)) ∧
      (∀ i, ‖(a i : ℂ)‖ ≤ (residueCardinality v.1 : ℝ) ^ A₀) ∧
      (∀ j, ‖((c j : ℂ))⁻¹‖ ≤ (residueCardinality v.1 : ℝ) ^ B₀) ∧
      (partialEulerFactor P P' hP hP' v (1 + s))⁻¹ =
        ∏ i, ∏ j, (1 - (a i : ℂ) * ((c j : ℂ))⁻¹ *
          (residueCardinality v.1 : ℂ) ^ (-(1 + s))) := by
    intro v
    obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
      (P.spectralSystem.eigenvalues v.1 fun h => v.2 (hP h))
    obtain ⟨c, hc⟩ := Unramified.Eigenvalues.ofTuple_surjective (t + 1)
      (Pd.spectralSystem.eigenvalues v.1 fun h => v.2 (hPd h))
    obtain ⟨hb, hE⟩ := partialEulerFactor_inv_eq P P' Pd hP hP' hPd hcontra v a ha c hc (1 + s)
    refine ⟨a, c, ha, hc, fun i => ?_, fun j => ?_, hE⟩
    · exact hA₀ v.1 (fun h => v.2 (hP h)) (a i) (by rw [← ha]; exact Langlands.Global.RankinSelbergGlobal.EqualEulerLocal.mem_ofTuple a i)
    · have h := hB₀ v.1 (fun h => v.2 (hP' h)) ((c j)⁻¹)
        (by rw [hb]; exact Langlands.Global.RankinSelbergGlobal.EqualEulerLocal.mem_ofTuple (fun j => (c j)⁻¹) j)
      rwa [Units.val_inv_eq_inv_val] at h
  have hL0 : ∀ v : {v : FinitePlace F // v ∉ S}, partialEulerFactor P P' hP hP' v (1 + s) ≠ 0 := by
    intro v h0
    obtain ⟨a, c, -, -, hba, hbc, hE⟩ := hdata v
    have h1 : (partialEulerFactor P P' hP hP' v (1 + s))⁻¹ = 0 := by rw [h0, inv_zero]
    rw [hE] at h1
    exact prod_ne_zero_of_bounds v.1 a c hba hbc hsAB h1
  have hsumE : Summable fun v : {v : FinitePlace F // v ∉ S} =>
      ‖(partialEulerFactor P P' hP hP' v (1 + s))⁻¹ - 1‖ := by
    have hev : ∀ᶠ v in Filter.cofinite,
        ‖partialEulerFactor P P' hP hP' v (1 + s) - 1‖ ≤ 1 / 2 :=
      hsumL.tendsto_cofinite_zero.eventually (eventually_le_nhds (by norm_num))
    refine Summable.of_norm_bounded_eventually (hsumL.mul_left 2) ?_
    filter_upwards [hev] with v hv
    rw [norm_norm]
    exact CuspidalPairEulerConvergence.norm_inv_sub_one_le hv
  have hprodE := CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one hsumE
  have hone : partialEulerProduct P P' hP hP' (1 + s) *
      ∏' v : {v : FinitePlace F // v ∉ S}, (partialEulerFactor P P' hP hP' v (1 + s))⁻¹ = 1 := by
    have h := hprodL.mul hprodE
    have e : (fun v : {v : FinitePlace F // v ∉ S} =>
        partialEulerFactor P P' hP hP' v (1 + s) * (partialEulerFactor P P' hP hP' v (1 + s))⁻¹) =
        fun _ => (1 : ℂ) :=
      funext fun v => mul_inv_cancel₀ (hL0 v)
    rw [e] at h
    exact h.unique hasProd_one
  let : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  have : (openCellHaar F r t).IsAddLeftInvariant := openCellHaar_isAddLeftInvariant
  have hstep : ∀ A : Finset (FinitePlace F), S ⊆ A → ∀ v : {v : FinitePlace F // v ∉ S},
      ∀ hv : v.1 ∉ A,
      ∫ Y in integralOutside F r t (Finset.cons v.1 A hv), openCellIntegrand ψ.complex φ s Y
          ∂(openCellHaar F r t) =
        (partialEulerFactor P P' hP hP' v (1 + s))⁻¹ *
          ∫ Y in integralOutside F r t A, openCellIntegrand ψ.complex φ s Y
            ∂(openCellHaar F r t) := by
    intro A _hSA v hv
    obtain ⟨ψv, hcan, hcond⟩ := hS v.1 v.2
    obtain ⟨a, c, ha, hc, hba, hbc, hE⟩ := hdata v
    have hϖ := RankinSelbergGlobal.LocalPointFactorization.isUniformizingElement_canonical v.1
    have hloc := hσA _ (CompletionPadic.padicField v.1) ψv hcond
      (RankinSelbergGlobal.LocalPointFactorization.placeUniformizer v.1) hϖ a c hba hbc s hsA
      (Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s)
      (fun X m₁ m₂ k hk => Shahidi.UnramifiedSection.sectionFunction_law hϖ a c s hcond X m₁ m₂ k hk)
    rw [hE]
    refine setIntegral_cons_eq_mul (openCellHaar F r t) A v.1 hv hint.integrableOn hloc ?_
    intro y Z hZ
    exact openCellIntegrand_localMatrix_add P Pd hP hPd ψ hψF hS hφ hsph s v.1 v.2 ψv hcan hcond _
      hϖ a ha c hc Z (fun i j => hZ v.1 hv i j) (Quotient.out y)
  have hex := integral_eq_hasProd_mul_setIntegral (openCellHaar F r t) S hint hprodE hstep
  rw [openCellIntegral_eq_integral]
  change partialEulerProduct P P' hP hP' (1 + s) *
      ∫ Y, openCellIntegrand ψ.complex φ s Y ∂(openCellHaar F r t) =
    ∫ Y in integralOutside F r t S, openCellIntegrand ψ.complex φ s Y ∂(openCellHaar F r t)
  rw [hex, ← mul_assoc, hone, one_mul]

end Langlands.Global
