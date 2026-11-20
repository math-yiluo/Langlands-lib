import Langlands.Global.RankinSelberg.ArchimedeanSchwartzAssembly
import Langlands.Global.RankinSelberg.EqualAnalyticDominated
import Langlands.Global.RankinSelberg.EqualAnalyticRowMeasure
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # A product Schwartz function detecting both equal-rank residues -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open NumberField MeasureTheory Set

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open EqualAnalytic EqualSchwartzTensor SchwartzBruhatProof

private theorem exists_nonnegative_schwartz (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ (φ : SchwartzMap E ℂ) (f : E → ℝ), (∀ x, φ x = (f x : ℂ)) ∧
      (∀ x, 0 ≤ f x) ∧ f 0 = 1 := by
  obtain ⟨f, _, hfc, hfs, hfn, hf₀⟩ :=
    exists_contDiff_tsupport_subset (E := E) (s := Set.univ) (x := 0) (n := ⊤) Filter.univ_mem
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ f) := hfc.comp_left rfl
  let φ : SchwartzMap E ℂ := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hfs)
  exact ⟨φ, f, fun _ => rfl, fun x => (hfn ⟨x, rfl⟩).1, hf₀⟩

variable {F : Type u} [Field F] [NumberField F]

private def integralLocalRows (n : ℕ) (v : FinitePlace F) :
    AddSubgroup (Fin n → FiniteCompletion F v) :=
  AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toAddSubgroup

private theorem isOpen_integralLocalRows (n : ℕ) (v : FinitePlace F) :
    IsOpen (integralLocalRows n v : Set (Fin n → FiniteCompletion F v)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

private theorem isCompact_integralLocalRows (n : ℕ) (v : FinitePlace F) :
    IsCompact (integralLocalRows n v : Set (Fin n → FiniteCompletion F v)) :=
  isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers F v

/-- Both origin values can be nonzero for a Schwartz–Bruhat tensor of local factors,
with the standard finite factors outside the prescribed set. -/
def PureSchwartzOriginWitnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (n : ℕ) (S : Finset (FinitePlace F)) (ψ : AddChar (Adeles F) ℂ),
    ∃ (φR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
      (φC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
      (φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ),
      (∀ v ∈ S, IsLocallyConstant (φv v) ∧ HasCompactSupport (φv v)) ∧
      let φ := restrictedTensor F n S φR φC φv
      φ ∈ schwartzBruhat F n ∧ IsStandardOutside F n S φ ∧
      φ 0 = 1 ∧ 0 < (fourierTransform F n ψ φ 0).re

theorem pureSchwartzOriginWitness : PureSchwartzOriginWitnessStatement.{u} := by
  classical
  intro F _ _ _ n S ψ
  obtain ⟨ρ, f, hρ, hf, hf₀⟩ := exists_nonnegative_schwartz (Fin n → ℝ)
  obtain ⟨χ, g, hχ, hg, hg₀⟩ := exists_nonnegative_schwartz (Fin n → ℂ)
  let φR (_ : {v : InfinitePlace F // v.IsReal}) := ρ
  let φC (_ : {v : InfinitePlace F // v.IsComplex}) := χ
  let φv (v : FinitePlace F) := cosetIndicator (integralLocalRows n v) 0
  have hφv (v : FinitePlace F) (_ : v ∈ S) :
      IsLocallyConstant (φv v) ∧ HasCompactSupport (φv v) :=
    ⟨isLocallyConstant_cosetIndicator _ (isOpen_integralLocalRows n v) _,
      hasCompactSupport_cosetIndicator _ (isOpen_integralLocalRows n v)
        (isCompact_integralLocalRows n v) _⟩
  let φ := restrictedTensor F n S φR φC φv
  have hφ : φ ∈ schwartzBruhat F n := restrictedTensor_mem_schwartzBruhat F n S φR φC φv hφv
  have hstd : IsStandardOutside F n S φ := restrictedTensor_isStandardOutside F n S φR φC φv
  have hzero : (0 : RowVector F n) ∈ integralOutside F n S := by
    intro v _ j
    simpa only [localCoordinates, Matrix.zero_apply, map_zero] using
      (v.adicCompletionIntegers F).zero_mem
  have hφ₀ : φ 0 = 1 := by
    have harch : archimedeanCoordinates F n 0 = 0 := by
      funext j
      change (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have hreal (v : {v : InfinitePlace F // v.IsReal}) :
        (fun _ : Fin n => (0 : mixedEmbedding.mixedSpace F).1 v) = 0 := rfl
    have hcomplex (v : {v : InfinitePlace F // v.IsComplex}) :
        (fun _ : Fin n => (0 : mixedEmbedding.mixedSpace F).2 v) = 0 := rfl
    have hlocal (v : FinitePlace F) : localCoordinates F n v 0 = 0 := by
      funext j
      simp only [localCoordinates, Matrix.zero_apply, map_zero, Pi.zero_apply]
    simp only [φ, restrictedTensor, Set.indicator_of_mem hzero, archimedeanTensor_apply, harch,
      Pi.zero_apply, hreal, hcomplex, φR, φC, hρ, hχ, hf₀, hg₀, Complex.ofReal_one, Finset.prod_const_one,
      φv, hlocal, cosetIndicator, sub_zero, zero_mem, ite_true, mul_one]
  have hcast (x : RowVector F n) : ∃ t : ℝ, 0 ≤ t ∧ φ x = (t : ℂ) := by
    by_cases hx : x ∈ integralOutside F n S
    · let y := archimedeanCoordinates F n x
      let b (v : FinitePlace F) : ℝ := if localCoordinates F n v x ∈ integralLocalRows n v
        then 1 else 0
      have hb (v : FinitePlace F) : φv v (localCoordinates F n v x) = (b v : ℂ) := by
        simp only [φv, cosetIndicator, sub_zero, b]
        split_ifs <;> simp
      refine ⟨((∏ v : {v : InfinitePlace F // v.IsReal}, f (fun j => (y j).1 v)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, g (fun j => (y j).2 v)) *
        ∏ v ∈ S, b v, ?_, ?_⟩
      · refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => hf _)
          (Finset.prod_nonneg fun v _ => hg _)) (Finset.prod_nonneg fun v _ => ?_)
        dsimp [b]
        split_ifs <;> norm_num
      · simp only [φ, restrictedTensor, Set.indicator_of_mem hx, archimedeanTensor_apply,
          φR, φC, hρ, hχ, hb, ← Complex.ofReal_prod, ← Complex.ofReal_mul, y]
    · exact ⟨0, le_rfl, by simp [φ, restrictedTensor, hx]⟩
  let φreal (x : RowVector F n) := (φ x).re
  have hφco : φ = (fun x => (φreal x : ℂ)) := by
    funext x
    obtain ⟨t, _, ht⟩ := hcast x
    simp only [φreal, ht, Complex.ofReal_re]
  have hnn (x : RowVector F n) : 0 ≤ φreal x := by
    obtain ⟨t, ht, he⟩ := hcast x
    simpa only [φreal, he, Complex.ofReal_re] using ht
  have hφreal₀ : φreal 0 = 1 := by simp [φreal, hφ₀]
  obtain ⟨hcon, hin, _⟩ := schwartzBruhat_properties F n hφ
  have hpos := integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp hcon) hin.re hnn (hφreal₀.trans_ne one_ne_zero)
  refine ⟨φR, φC, φv, hφv, hφ, hstd, hφ₀, ?_⟩
  change 0 < (fourierTransform F n ψ φ 0).re
  rw [hφco]
  simpa only [fourierTransform, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    AddChar.map_zero_eq_one, mul_one, integral_complex_ofReal, Complex.ofReal_re,
    φreal, Function.comp_apply] using hpos

end Langlands.Global.RankinSelbergGlobal.SelfPair
