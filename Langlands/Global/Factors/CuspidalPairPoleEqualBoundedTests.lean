import Langlands.Global.Factors.CuspidalPairPoleEqualTestFamily
import Langlands.Global.Factors.CuspidalPairPoleStripSums

/-! # Bounded combinations of actual normalized equal-rank tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField Set
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelbergGlobal InfiniteWhittakerSlice
open FiniteWhittakerDual ArchimedeanLocal LocalFactor.Archimedean
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

private theorem boundedSum_of_sum_eq_one {J : Type*} [Fintype J] {f : J → ℂ → ℂ}
    (h : ∀ s, ∑ i, f i s = 1) : HasBoundedNormalizedSum f := by
  refine ⟨Finset.univ, fun _ _ => 1, ?_, fun s _ => ?_⟩
  · intro i hi a b ε hε
    exact ⟨1, fun _ _ _ _ _ => (norm_one (α := ℂ)).le⟩
  · simpa only [one_mul] using h s

private theorem boundedSum_scale {J : Type*} {f g : J → ℂ → ℂ} (A : J → ℂ)
    (hA : ∀ i, A i ≠ 0) (hfg : ∀ i s, g i s = A i * f i s)
    (h : HasBoundedNormalizedSum f) : HasBoundedNormalizedSum g := by
  obtain ⟨B, w, hw, hSum⟩ := h
  refine ⟨B, fun i s => (A i)⁻¹ * w i s, ?_, fun s hs => ?_⟩
  · intro i hi a b ε hε
    obtain ⟨C, hC⟩ := hw i hi a b ε hε
    refine ⟨‖(A i)⁻¹‖ * C, fun s ha hb h0 h1 => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC s ha hb h0 h1) (norm_nonneg _)
  · refine (Finset.sum_congr rfl fun i _ => ?_).trans (hSum s hs)
    rw [hfg i s, ← mul_assoc, mul_right_comm ((A i)⁻¹) (w i s) (A i),
      inv_mul_cancel₀ (hA i), one_mul]

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)} {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance eqBoundedAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance eqBoundedSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- Actual equal-rank partial integrals with a bounded weighted normalization sum. -/
def HasBoundedEqualPartialTests (c : FinitePairLChoice P P' hP hP')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) : Prop :=
  ∃ (J : Type u) (test : J → NormalizedEqualPoleTest c S ψ Linf),
    HasBoundedNormalizedSum (fun i => (test i).2.value)

/-- Combine finite ordinary normalized sums at the infinite places with the Laurent
combinations at the specified finite places, and realize each tuple globally. -/
theorem hasBoundedEqualPartialTests_of_local (c : FinitePairLChoice P P' hP hP')
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
      (realOrdinaryEqualTest r (dR v) (dR' v) (aR v) (realQuotientMeasureData r)) (realPairLFactor (dR v) (dR' v)))
    (hAc : ∀ w, HasFiniteOrdinaryNormalizationSum
      (complexOrdinaryEqualTest r (dC w) (dC' w) (aC w) (complexQuotientMeasureData r))
      (complexPairLFactor (dC w) (dC' w))) :
    HasBoundedEqualPartialTests c S ψ (archimedeanPairProduct dR dR' dC dC') := by
  simp only [HasFiniteOrdinaryNormalizationSum] at hAr hAc
  choose nR R NR hNR using hAr
  choose nC C NC hNC using hAc
  have hF (v : S) := (poleFiniteBoundedTestFamilies v.1 (ψv v) c (ν v) hT hT').1 rfl
  choose JS D ΦS NS hNS using hF
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
  have hLocal (p : Place) : HasBoundedNormalizedSum (normalized p) := by
    rcases p with v | (w | v)
    · exact boundedSum_of_sum_eq_one (hNR v)
    · exact boundedSum_of_sum_eq_one (hNC w)
    · exact hNS v
  let J := ∀ p : Place, LocalTest p
  let f (i : J) (s : ℂ) := ∏ p, normalized p (i p) s
  have hProduct : HasBoundedNormalizedSum f := HasBoundedNormalizedSum.prod hLocal
  have hRealize (i : J) :
      ∃ (A : ℂ) (j : NormalizedEqualPoleTest c S ψ (archimedeanPairProduct dR dR' dC dC')),
        A ≠ 0 ∧ ∀ s, j.2.value s = A * f i s := by
    obtain ⟨x, x', Φ, hx, hx', hΦ, hstd, N, A, hA, hValue⟩ :=
      exists_normalizedEqualPureTest_of_prescribed c hPS hPS' hψF hS hψv M M'
        aR aC dR dR' dC dC' hR hR'
        (fun v => R v (i (.inl v))) (fun w => C w (i (.inr (.inl w))))
        (fun v => NR v (i (.inl v))) (fun w => NC w (i (.inr (.inl w))))
        (fun v => D v (i (.inr (.inr v)))) (fun v => ΦS v (i (.inr (.inr v))))
        (fun v => NS v (i (.inr (.inr v))))
    refine ⟨A, ⟨⟨x, x', Φ, hx, hx', hΦ, hstd⟩, N⟩, hA, fun s => ?_⟩
    change N.value s = A * f i s
    rw [hValue s]
    congr 1
    simp only [f, Place, Fintype.prod_sum_type, normalized, mul_assoc]
  choose A test hA hValue using hRealize
  exact ⟨J, test, boundedSum_scale A hA hValue hProduct⟩

end Langlands.Global.CuspidalPairPoles
