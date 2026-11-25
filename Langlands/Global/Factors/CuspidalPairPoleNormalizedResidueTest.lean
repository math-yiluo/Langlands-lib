import Langlands.Global.Factors.CuspidalPairPoleEqualSpanNormalization
import Langlands.Global.RankinSelberg.SelfPairPureSchwartz
import Langlands.Global.RankinSelberg.SelfPairResidue
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # An ordinary normalized test detecting the conjugate equal-rank residues -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelbergGlobal RankinSelbergGlobal.EqualSchwartzTensor
open LocalFactor.Archimedean FiniteWhittakerDual InfiniteWhittakerSlice
open CuspidalPairFunctionalEquation
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T.conjugate} {P' : CuspidalSpectralPresentation.{u, uQ} T}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance poleResidueSchemeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleResidueSchemeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleResidueRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleResidueContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleResidueFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleResidueAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleResidueStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- The actual conjugate vector pair and a Schwartz test detecting both origin values
have an entire ordinary partial-integral normalization. -/
def HasNormalizedConjugateResidueTest (c : FinitePairLChoice P P' hP hP')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) : Prop :=
  ∃ (x : T.Space) (Φ : RowVector F (r + 1) → ℂ),
    x ≠ 0 ∧ IsSphericalOutside F T.conjugate S (T.conjugateEquiv x) ∧ IsSphericalOutside F T S x ∧
    Φ ∈ schwartzBruhat F (r + 1) ∧ IsStandardOutside F (r + 1) S Φ ∧
    Φ 0 ≠ 0 ∧ fourierTransform F (r + 1) ψ.complex Φ 0 ≠ 0 ∧
    Nonempty (OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T.conjugate ψ.complex (T.conjugateEquiv x))
        (cuspWhittaker F T ψ.complex⁻¹ x) Φ)
      (fun s => Linf s * ∏ v ∈ S, c.finiteL v s))

/-- A residue test with conjugate vectors can be normalized after a joint enlargement
of the finite set, using the ordinary local continuation and slice range results. -/
theorem exists_normalizedConjugateResidueTest_placewise
    (c : FinitePairLChoice P P' hP hP') (hT : IsTrivialOnSplitCentre T)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hNR : Nonempty RP → RealEqualOrdinaryNormalizedContinuationAt r) (hNC : ComplexEqualOrdinaryNormalizedContinuationAt r)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, T.conjugate.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.conjugate.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T.realization.HasComplexPlaceParameter w (dC' w))
    (B : Finset (FinitePlace F)) :
    ∃ S : Finset (FinitePlace F), B ⊆ S ∧ P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      HasNormalizedConjugateResidueTest c S ψ (archimedeanPairProduct dR dR' dC dC') := by
  obtain ⟨x, g, hg⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  have hx : x ≠ 0 := by
    intro h
    apply hg
    rw [h, map_zero]
    rfl
  obtain ⟨A, hA⟩ := exists_finiteAdditiveSupport ψ hψF
  obtain ⟨U, hBU, hPU, hLeft⟩ := exists_mem_poleEqualPureSpan P hP (B ∪ A) (T.conjugateEquiv x)
  obtain ⟨S, hUS, hP'S, hRight⟩ := exists_mem_poleEqualPureSpan P' hP' U x
  have hPS := hPU.trans hUS
  have hS := finiteAdditiveSupport_mono hA (Finset.subset_union_right.trans (hBU.trans hUS))
  have hLeftS := poleEqualPureSpan_mono P hP hPU hPS hUS hLeft
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψF v.1
  have hψv (v : S) : IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v) :=
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψF v.1
  let ν (v : S) : LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v) :=
    ⟨Correspondence.localSelfDualHaar (padicField v.1) (ψv v),
      Correspondence.isSelfDual_localSelfDualHaar (padicField v.1) (ψv v)⟩
  obtain ⟨ΦR, ΦC, Φv, hΦv, _, _, h0, h1⟩ := SelfPair.pureSchwartzOriginWitness F (r + 1) S ψ.complex
  let ΦS (v : S) : finiteRowTest F (r + 1) v.1 := by
    refine ⟨Φv v.1, ?_, ?_⟩
    · exact (completion_row_topology_eq F (r + 1) v.1) ▸ (hΦv v.1 v.2).1
    · exact (completion_row_topology_eq F (r + 1) v.1) ▸ (hΦv v.1 v.2).2
  let Φ := poleEqualSchwartzTensor ΦR ΦC ΦS
  have hΦeq : Φ = restrictedTensor F (r + 1) S ΦR ΦC Φv := by
    unfold Φ poleEqualSchwartzTensor
    rw [restrictedTensor_eq, restrictedTensor_eq]
    exact congrArg (Set.indicator (integralOutside F (r + 1) S)) (funext fun y => by
      apply congrArg (fun z : ℂ => ((∏ v, ΦR v (realRowCoordinates F (r + 1) v y)) *
        ∏ w, ΦC w (complexRowCoordinates F (r + 1) w y)) * z)
      exact Finset.prod_congr rfl fun v _ => congrFun (extendFiniteRowTests_apply F (r + 1) S ΦS v) _)
  have hΦ := poleEqualSchwartzTensor_spec ΦR ΦC ΦS
  let Linf := archimedeanPairProduct dR dR' dC dC'
  have hNorm := hasOrdinaryEqualNormalizationsOnPureSpans c hPS hP'S hψF hS Φ hΦ.1 hΦ.2 Linf
    (fun a a' b b' => exists_ordinaryEqualNormalization_of_pure_tensors_placewise c hPS hP'S
      (SelfPair.isTrivialOnSplitCentre_conjugate T hT) hT hψF hS hψv ν hNR hNC M M' aR aC
      dR dR' dC dC' hR hR' hdR hdR' hdC hdC' a a' b b' ΦR ΦC ΦS)
  refine ⟨S, Finset.subset_union_left.trans (hBU.trans hUS), hPS, hP'S, hS,
    x, Φ, hx, sphericalOutside_of_mem_poleEqualPureSpan P hP hPS hLeftS,
    sphericalOutside_of_mem_poleEqualPureSpan P' hP' hP'S hRight, hΦ.1, hΦ.2, ?_, ?_,
    hNorm (T.conjugateEquiv x) x hLeftS hRight⟩
  · rw [hΦeq, h0]
    exact one_ne_zero
  · rw [hΦeq]
    intro hz
    rw [hz, Complex.zero_re] at h1
    exact (lt_irrefl 0) h1


theorem exists_normalizedConjugateResidueTest_of_local_at
    (c : FinitePairLChoice P P' hP hP') (hT : IsTrivialOnSplitCentre T)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hNR : RealEqualOrdinaryNormalizedContinuationAt r) (hNC : ComplexEqualOrdinaryNormalizedContinuationAt r)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, T.conjugate.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.conjugate.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T.realization.HasComplexPlaceParameter w (dC' w))
    (B : Finset (FinitePlace F)) :
    ∃ S : Finset (FinitePlace F), B ⊆ S ∧ P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      HasNormalizedConjugateResidueTest c S ψ (archimedeanPairProduct dR dR' dC dC') :=
  exists_normalizedConjugateResidueTest_placewise c hT hψF (fun _ => hNR) hNC M M' aR aC
    dR dR' dC dC' hR hR' hdR hdR' hdC hdC' B

/-- A residue test with conjugate vectors can be normalized after a joint enlargement
of the finite set, using the ordinary local continuation and slice range results. -/
theorem exists_normalizedConjugateResidueTest_of_local
    (c : FinitePairLChoice P P' hP hP') (hT : IsTrivialOnSplitCentre T)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hNR : RealOrdinaryNormalizedContinuationStatement) (hNC : ComplexOrdinaryNormalizedContinuationStatement)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, T.conjugate.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.conjugate.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T.realization.HasComplexPlaceParameter w (dC' w))
    (B : Finset (FinitePlace F)) :
    ∃ S : Finset (FinitePlace F), B ⊆ S ∧ P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      HasNormalizedConjugateResidueTest c S ψ (archimedeanPairProduct dR dR' dC dC') :=
  exists_normalizedConjugateResidueTest_of_local_at c hT hψF (hNR.2 r) (hNC.2 r) M M' aR aC
    dR dR' dC dC' hR hR' hdR hdR' hdC hdC' B

end Langlands.Global.CuspidalPairPoles
