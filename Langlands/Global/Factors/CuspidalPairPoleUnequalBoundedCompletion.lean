import Langlands.Global.Factors.CuspidalPairBoundedSumCompletion
import Langlands.Global.Factors.CuspidalPairFiniteEulerContinuity
import Langlands.Global.Factors.CuspidalPairPoleUnequalTestGrowth

/-! # Unequal-rank completions from finite ordinary normalization sums -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000

universe u uQ

open NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelbergGlobal InfiniteWhittakerSlice
open FiniteWhittakerDual ArchimedeanLocal LocalFactor.Archimedean
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u,uQ} T} {P' : CuspidalSpectralPresentation.{u,uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)} {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance unequalBoundedAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalBoundedSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

private structure NormalizedUnequalTest (c : FinitePairLChoice P P' hP hP') (hrt : t < r)
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) where
  left : T.Space
  right : T'.Space
  sphericalLeft : IsSphericalOutside F T S left
  sphericalRight : IsSphericalOutside F T' S right
  normalization : OrdinaryIntegralNormalization
    (partialUnequalWhittakerIntegral F hrt S
      (cuspWhittaker F T ψ.complex left) (cuspWhittaker F T' ψ.complex⁻¹ right))
    (fun s => Linf s * ∏ v ∈ S, c.finiteL v s)

/-- An unequal-rank completion with the prescribed factors and vertical-strip bounds. -/
def HasUnequalBoundedCompletion (c : FinitePairLChoice P P' hP hP') (Linf : ℂ → ℂ) : Prop :=
  ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧
    HasSimplePoleProfile Λ False ∧ IsBoundedInVerticalStrips Λ

/-- Finite ordinary normalization sums, supplied at each infinite place, give the
bounded unequal-rank completion by unfolding the actual tests. -/
theorem hasUnequalBoundedCompletion_of_local_sums
    (c : FinitePairLChoice P P' hP hP') (hrt : t < r)
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hAr : ∀ v, HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest hrt (dR v) (dR' v) (aR v) (realQuotientMeasureData t))
      (realPairLFactor (dR v) (dR' v)))
    (hAc : ∀ w, HasFiniteOrdinaryNormalizationSum
      (complexOrdinaryUnequalTest hrt (dC w) (dC' w) (aC w) (complexQuotientMeasureData t))
      (complexPairLFactor (dC w) (dC' w))) :
    HasUnequalBoundedCompletion c (archimedeanPairProduct dR dR' dC dC') := by
  let k := r - (t + 1)
  have hr : r = t + (0 + k + 1) := by dsimp [k]; omega
  let Linf := archimedeanPairProduct dR dR' dC dC'
  have hCover (s : ℂ) : ∃ x : NormalizedUnequalTest c hrt S ψ Linf, x.normalization.value s ≠ 0 := by
    choose R NR hNR using fun v => HasFiniteOrdinaryNormalizationSum.covering
      (realOrdinaryUnequalTest hrt (dR v) (dR' v) (aR v) (realQuotientMeasureData t))
      (realPairLFactor (dR v) (dR' v)) (hAr v) s
    choose C NC hNC using fun w => HasFiniteOrdinaryNormalizationSum.covering
      (complexOrdinaryUnequalTest hrt (dC w) (dC' w) (aC w) (complexQuotientMeasureData t))
      (complexPairLFactor (dC w) (dC' w)) (hAc w) s
    choose D NS hNS using fun v : S => exists_poleFiniteUnequalTest v.1 (ψv v) c (ν v) hr hT hT' s
    obtain ⟨x, x', hx, hx', N, A, hA, hValue⟩ :=
      exists_normalizedUnequalPureTest_of_prescribed c hrt hr hPS hPS' hψF hS hψv ν
        M M' aR aC dR dR' dC dC' hR hR' R C NR NC D NS
    refine ⟨⟨x, x', hx, hx', N⟩, ?_⟩
    change N.value s ≠ 0
    rw [hValue]
    exact mul_ne_zero hA (mul_ne_zero
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hNR v)
        (Finset.prod_ne_zero_iff.mpr fun w _ => hNC w))
      (Finset.prod_ne_zero_iff.mpr fun v _ => (hNS v).1))
  let U : UnequalNormalizedTests.{u,uQ,u} c hrt S ψ Linf :=
    ⟨NormalizedUnequalTest c hrt S ψ Linf, (·.left), (·.right), (·.sphericalLeft), (·.sphericalRight),
      (·.normalization.value), (·.normalization.analytic), hCover,
      fun i => by
        obtain ⟨σ, hσ⟩ := i.normalization.eq_on_right
        exact ⟨σ, fun s hs => (hσ s hs).trans (mul_assoc _ _ _).symm⟩⟩
  simp only [HasFiniteOrdinaryNormalizationSum] at hAr hAc
  choose nR R NR hNR using hAr
  choose nC C NC hNC using hAc
  have hF (v : S) := (poleFiniteBoundedTestFamilies v.1 (ψv v) c (ν v) hT hT').2 k hr
  choose JS D NS hNS using hF
  let Place := RP ⊕ (CP ⊕ (S : Type u))
  let LocalTest : Place → Type
    | .inl v => Fin (nR v)
    | .inr (.inl w) => Fin (nC w)
    | .inr (.inr v) => JS v
  let normalized (p : Place) : LocalTest p → ℂ → ℂ :=
    match p with
    | .inl v => fun i => (NR v i).value
    | .inr (.inl w) => fun i => (NC w i).value
    | .inr (.inr v) => fun i => (NS v i).value
  have hFinite {J : Type} [Fintype J] {f : J → ℂ → ℂ} (hf : ∀ s, ∑ i, f i s = 1) :
      HasBoundedNormalizedSum f :=
    ⟨Finset.univ, fun _ _ => 1, fun _ _ _ _ _ _ =>
      ⟨1, fun _ _ _ _ _ => (norm_one (α := ℂ)).le⟩, fun s _ => by simpa only [one_mul] using hf s⟩
  have hLocal (p : Place) : HasBoundedNormalizedSum (normalized p) := by
    rcases p with v | (w | v)
    · exact hFinite (hNR v)
    · exact hFinite (hNC w)
    · exact hNS v
  let J := ∀ p : Place, LocalTest p
  let f (i : J) (s : ℂ) := ∏ p, normalized p (i p) s
  have hProduct : HasBoundedNormalizedSum f := HasBoundedNormalizedSum.prod hLocal
  have hRealize (i : J) :
      ∃ (A : ℂ) (j : U.Test), A ≠ 0 ∧ ∀ s, U.normalized j s = A * f i s := by
    obtain ⟨x, x', hx, hx', N, A, hA, hValue⟩ :=
      exists_normalizedUnequalPureTest_of_prescribed c hrt hr hPS hPS' hψF hS hψv ν
        M M' aR aC dR dR' dC dC' hR hR'
        (fun v => R v (i (.inl v))) (fun w => C w (i (.inr (.inl w))))
        (fun v => NR v (i (.inl v))) (fun w => NC w (i (.inr (.inl w))))
        (fun v => D v (i (.inr (.inr v)))) (fun v => NS v (i (.inr (.inr v))))
    refine ⟨A, ⟨x, x', hx, hx', N⟩, hA, fun s => ?_⟩
    change N.value s = A * f i s
    rw [hValue s]
    congr 1
    simp only [f, Place, Fintype.prod_sum_type, normalized, mul_assoc]
  choose A realize hA hValue using hRealize
  refine unequalBoundedSumCompletion U hψF hPS hPS' hS
    (exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC' c.rightHalfPlaneContinuous)
    (fun j => U.normalized (realize j)) realize (fun _ => rfl) ?_
  obtain ⟨Q, w, hw, hSum⟩ := hProduct
  refine ⟨Q, fun i s => (A i)⁻¹ * w i s, ?_, fun s hs => ?_⟩
  · intro i hi a b ε hε
    obtain ⟨C, hC⟩ := hw i hi a b ε hε
    refine ⟨‖(A i)⁻¹‖ * C, fun s ha hb h0 h1 => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC s ha hb h0 h1) (norm_nonneg _)
  · refine (Finset.sum_congr rfl fun i _ => ?_).trans (hSum s hs)
    change ((A i)⁻¹ * w i s) * U.normalized (realize i) s = w i s * f i s
    rw [hValue i s, ← mul_assoc, mul_right_comm ((A i)⁻¹) (w i s) (A i),
      inv_mul_cancel₀ (hA i), one_mul]

end Langlands.Global.CuspidalPairPoles
