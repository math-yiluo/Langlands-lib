import Langlands.Global.Factors.CuspidalPairPoleEqualCover
import Langlands.Global.Factors.CuspidalPairPoleNormalizedResidueTest

/-! # A family containing the ordinary normalized covering and residue tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelbergGlobal InfiniteWhittakerSlice FiniteWhittakerDual
open LocalFactor.Archimedean CuspidalPairFunctionalEquation
open ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)} {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {Linf : ℂ → ℂ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance poleEqualFamilyAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleEqualFamilySmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleEqualFamilyRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualFamilyContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualFamilyFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualFamilyAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleEqualFamilyStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- An actual equal-rank test and an entire normalization of its ordinary partial integral. -/
def NormalizedEqualPoleTest (c : FinitePairLChoice P P' hP hP')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) : Type u :=
  Σ i : EqualPoleTest T T' S, OrdinaryIntegralNormalization
    (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex i.left)
      (cuspWhittaker F T' ψ.complex⁻¹ i.right) i.schwartz)
    (fun s => Linf s * ∏ v ∈ S, c.finiteL v s)

variable (c : FinitePairLChoice P P' hP hP')

/-- The family of all normalized tests retains any separately supplied growth or residue test. -/
def equalNormalizedFamily (h : HasCoveringEqualPartialTests c S ψ Linf) :
    EqualNormalizedTestFamily c S ψ Linf where
  Test := NormalizedEqualPoleTest c S ψ Linf
  test := Sigma.fst
  normalized i := i.2.value
  analytic i := i.2.analytic
  nonvanishing s := by
    obtain ⟨x, x', Φ, hx, hx', hΦ, hstd, N, hN⟩ := h s
    exact ⟨⟨⟨x, x', Φ, hx, hx', hΦ, hstd⟩, N⟩, hN⟩
  partial_eq i := by
    obtain ⟨a, ha⟩ := i.2.eq_on_right
    exact ⟨a, fun s hs => (ha s hs).trans (mul_assoc _ _ _).symm⟩

private def ConjugateResidueTestFor (S : Finset (FinitePlace F))
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (Linf : ℂ → ℂ)
    (e : T = T'.conjugate) : Prop := by
  subst T
  exact HasNormalizedConjugateResidueTest c S ψ Linf

/-- Assemble the equal-rank family at a fixed set, including the conjugate residue
witness and a nonzero normalized test of exponential strip growth. -/
private theorem exists_equalNormalizedFamily_of_tests
    (hCov : HasCoveringEqualPartialTests c S ψ Linf)
    (hG : ∃ i : NormalizedEqualPoleTest c S ψ Linf,
      (∃ z, i.2.value z ≠ 0) ∧ HasStripExponentialGrowth i.2.value)
    (hRes : ∀ e : T = T'.conjugate, ConjugateResidueTestFor c S ψ Linf e) :
    ∃ D : EqualNormalizedTestFamily c S ψ Linf,
      (∃ i, (∃ z, D.normalized i z ≠ 0) ∧ HasStripExponentialGrowth (D.normalized i)) ∧
      ∀ e : T = T'.conjugate, ∃ i : D.Test,
        (D.test i).right ≠ 0 ∧
        (e ▸ (D.test i).left : T'.conjugate.Space) = T'.conjugateEquiv (D.test i).right ∧
        (D.test i).schwartz 0 ≠ 0 ∧ fourierTransform F (r + 1) ψ.complex (D.test i).schwartz 0 ≠ 0 := by
  refine ⟨equalNormalizedFamily c hCov, hG, ?_⟩
  intro e
  subst T
  have h : HasNormalizedConjugateResidueTest c S ψ Linf := hRes rfl
  obtain ⟨x, Φ, hx, hL, hR, hΦ, hstd, h0, h1, ⟨N⟩⟩ := h
  let i : NormalizedEqualPoleTest c S ψ Linf := ⟨⟨T'.conjugateEquiv x, x, Φ, hL, hR, hΦ, hstd⟩, N⟩
  exact ⟨i, hx, rfl, h0, h1⟩

/-- Given the actual local slice ranges, ordinary local continuation and generation,
only the strip-growth test remains as a separate input to constructing the family. -/
theorem exists_equalNormalizedFamily_of_local
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hNR : RealOrdinaryNormalizedContinuationStatement) (hNC : ComplexOrdinaryNormalizedContinuationStatement)
    (hGR : RealOrdinaryNormalizedGenerationStatement) (hGC : ComplexOrdinaryNormalizedGenerationStatement)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, T.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T'.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T'.realization.HasComplexPlaceParameter w (dC' w))
    (hG : ∀ S : Finset (FinitePlace F), P.exceptional ⊆ S → P'.exceptional ⊆ S →
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
      ∃ i : NormalizedEqualPoleTest c S ψ (archimedeanPairProduct dR dR' dC dC'),
        (∃ z, i.2.value z ≠ 0) ∧ HasStripExponentialGrowth i.2.value) :
    let Linf := archimedeanPairProduct dR dR' dC dC'
    ∃ S : Finset (FinitePlace F), P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∃ D : EqualNormalizedTestFamily c S ψ Linf,
        (∃ i, (∃ z, D.normalized i z ≠ 0) ∧ HasStripExponentialGrowth (D.normalized i)) ∧
        ∀ e : T = T'.conjugate, ∃ i : D.Test,
          (D.test i).right ≠ 0 ∧
          (e ▸ (D.test i).left : T'.conjugate.Space) = T'.conjugateEquiv (D.test i).right ∧
          (D.test i).schwartz 0 ≠ 0 ∧ fourierTransform F (r + 1) ψ.complex (D.test i).schwartz 0 ≠ 0 := by
  intro Linf
  have hParts : ∃ S : Finset (FinitePlace F), P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∀ e : T = T'.conjugate, ConjugateResidueTestFor c S ψ Linf e := by
    by_cases h : T = T'.conjugate
    · subst T
      have hex := exists_normalizedConjugateResidueTest_of_local c hT' hψF hNR hNC M M' aR aC
        dR dR' dC dC' hR hR' hdR hdR' hdC hdC' ∅
      refine ⟨hex.choose, hex.choose_spec.2.1, hex.choose_spec.2.2.1, hex.choose_spec.2.2.2.1, ?_⟩
      intro e
      change HasNormalizedConjugateResidueTest c hex.choose ψ Linf
      exact hex.choose_spec.2.2.2.2
    · obtain ⟨A, hA⟩ := exists_finiteAdditiveSupport ψ hψF
      let S := (P.exceptional ∪ P'.exceptional) ∪ A
      exact ⟨S, Finset.subset_union_left.trans Finset.subset_union_left,
        Finset.subset_union_right.trans Finset.subset_union_left,
        finiteAdditiveSupport_mono hA Finset.subset_union_right, fun e => (h e).elim⟩
  obtain ⟨S, hPS, hPS', hS, hRes⟩ := hParts
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψF v.1
  have hψv (v : S) : IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v) :=
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψF v.1
  let ν (v : S) : LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v) :=
    ⟨Correspondence.localSelfDualHaar (padicField v.1) (ψv v),
      Correspondence.isSelfDual_localSelfDualHaar (padicField v.1) (ψv v)⟩
  have hCov := exists_coveringEqualPureTest_of_local c hPS hPS' hT hT' hψF hS hψv ν
    hGR hGC M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC'
  exact ⟨S, hPS, hPS', hS, exists_equalNormalizedFamily_of_tests c hCov (hG S hPS hPS' hS) hRes⟩

end Langlands.Global.CuspidalPairPoles
