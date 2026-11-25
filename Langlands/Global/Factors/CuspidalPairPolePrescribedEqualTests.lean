import Langlands.Global.Factors.CuspidalPairPoleEqualNormalizedProduct
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.Factors.CuspidalPairPoleUnequalLocalTests
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.Global.Factors.CuspidalPairPolePrescribedFiniteTests

/-! # Ordinary normalization of arbitrary pure equal-rank adelic tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal ArchimedeanLocal
open LocalFactor.Archimedean
open InfiniteWhittakerSlice InfinitePlaceFamily FiniteWhittakerDual FiniteWhittakerSemilocal FiniteWhittakerTensor
open EqualSchwartzTensor
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance polePrescribedEqualAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance polePrescribedEqualSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance polePrescribedEqualRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance polePrescribedEqualContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance polePrescribedEqualFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance polePrescribedEqualAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance polePrescribedEqualStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- The actual cuspidal vector of specified retained finite and infinite pure factors. -/
def poleEqualPureVector (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : HasIrreducibleAdmissibleComponents P) (hPS : P.exceptional ⊆ S)
    (a : ∀ v : S, P.localFactor v) (b : ∀ i : Index F, T.placeDensityModels.subspace i) : T.Space :=
  P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)

/-- A pure vector with reference factors outside `S` is spherical there. -/
theorem poleEqualPureVector_sphericalOutside (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : HasIrreducibleAdmissibleComponents P) (hPS : P.exceptional ⊆ S)
    (a : ∀ v : S, P.localFactor v) (b : ∀ i : Index F, T.placeDensityModels.subspace i) :
    IsSphericalOutside F T S (poleEqualPureVector P hP hPS a b) :=
  P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS a _

/-- Ordinary real equal-rank continuation for the indicated rank. -/
def RealEqualOrdinaryNormalizedContinuationAt (r : ℕ) : Prop :=
  ∀ (d e : List RealBlock), realRank d = r + 1 → realRank e = r + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e)

/-- Ordinary complex equal-rank continuation for the indicated rank. -/
def ComplexEqualOrdinaryNormalizedContinuationAt (r : ℕ) : Prop :=
  ∀ (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e)

/-- Normalize the partial integral of any indicated pure equal-rank test using ordinary
local continuation for the specified coefficient models. -/
theorem exists_ordinaryEqualNormalization_of_pure_tensors_placewise
    (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (hNReal : Nonempty RP → RealEqualOrdinaryNormalizedContinuationAt r)
    (hNComplex : ComplexEqualOrdinaryNormalizedContinuationAt r)
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
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (b : ∀ i : Index F, T.placeDensityModels.subspace i)
    (b' : ∀ i : Index F, T'.placeDensityModels.subspace i)
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ) (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1) :
    let x := poleEqualPureVector P hP hPS a b
    let x' := poleEqualPureVector P' hP' hPS' a' b'
    Nonempty (OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') (poleEqualSchwartzTensor ΦR ΦC ΦS))
      (fun s => archimedeanPairProduct dR dR' dC dC' s * ∏ v ∈ S, c.finiteL v s)) := by
  intro x x'
  have hFinite (v : S) := exists_poleFiniteEqualNormalization_of_vectors v.1 (ψv v) c (ν v) hT hT'
    (a v) (a' v) (ΦS v)
  choose D hD hD' NS hNS using hFinite
  let WR (v : RP) := M.model (.inl v) (b (.inl v))
  let WR' (v : RP) := M'.model (.inl v) (b' (.inl v))
  let WC (w : CP) := M.model (.inr w) (b (.inr w))
  let WC' (w : CP) := M'.model (.inr w) (b' (.inr w))
  have hWR (v : RP) : WR v ∈ realWhittakerModel r (dR v) (aR v) :=
    hR.1 v ▸ LinearMap.mem_range_self _ (b (.inl v))
  have hWR' (v : RP) : WR' v ∈ realWhittakerModel r (dR' v) (-aR v) :=
    hR'.1 v ▸ LinearMap.mem_range_self _ (b' (.inl v))
  have hWC (w : CP) : WC w ∈ complexWhittakerModel r (dC w) (aC w) :=
    hR.2 w ▸ LinearMap.mem_range_self _ (b (.inr w))
  have hWC' (w : CP) : WC' w ∈ complexWhittakerModel r (dC' w) (-aC w) :=
    hR'.2 w ▸ LinearMap.mem_range_self _ (b' (.inr w))
  let NR (v : RP) := Classical.choice (hNReal ⟨v⟩ _ _ (hdR v).1 (hdR' v).1 (aR v)
    (realQuotientMeasureData r) (⟨WR v, hWR v⟩, ⟨WR' v, hWR' v⟩, ΦR v))
  let NC (w : CP) := Classical.choice (hNComplex _ _ (hdC w).1 (hdC' w).1 (aC w)
    (complexQuotientMeasureData r) (⟨WC w, hWC w⟩, ⟨WC' w, hWC' w⟩, ΦC w))
  have hPairR (v : RP) (u : GeneralLinear.upperUnipotent (r + 1) ℝ) (g : GeneralLinear (r + 1) ℝ) :
      WR v (u.val * g) * WR' v (u.val * g) = WR v g * WR' v g := by
    have hL := (RealLocalWhittaker.model_le_regularFunctions (dR v) (aR v) (hWR v)).1
    have hRight := (RealLocalWhittaker.model_le_regularFunctions (dR' v) (-aR v) (hWR' v)).1
    rw [hL _ u.property, hRight _ u.property, mul_mul_mul_comm,
      RealEqualConvergence.realWhittakerCharacter_mul_neg, one_mul]
  have hProd := exists_normalized_product (P := P) (hP := hP) ψ hψF S hPS hS ψv hψv
    (fun v => (D v).leftFactor.functional) (fun v => (D v).leftFactor.reference)
    (fun v => (D v).leftFactor.reference_value) M
  let ψ' := inverseCharacter ψ
  have hψ' (y : F) : ψ' (algebraMap F (Adeles F) y) = 1 := by
    change inverseCharacter ψ _ = 1
    rw [inverseCharacter_apply, hψF, inv_one]
  have hProd' := exists_normalized_product (P := P') (hP := hP') ψ' hψ' S hPS'
    (finiteAdditiveSupport_inverseCharacter ψ S hS) (fun v => inverseFinite v.1 (ψv v))
    (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v))
    (fun v => (D v).rightFactor.functional) (fun v => (D v).rightFactor.reference)
    (fun v => (D v).rightFactor.reference_value) M'
  let κ := hProd.choose_spec.choose
  let κ' := hProd'.choose_spec.choose
  have hInf : HasPrescribedInfiniteWhittakerProduct
      (infiniteResidual S P hP hPS ψ.complex (fun v => (D v).leftFactor.reference) (PiTensorProduct.tprod ℂ b))
      κ WR WC := by
    intro g
    refine (hProd.choose_spec.choose_spec.2.2.2 b g).trans ?_
    apply congrArg (fun z : ℂ => κ * z)
    let f (i : Index F) := M.model i (b i) (placeComponents (r + 1) g i)
    change (∏ i, f i) = (∏ v, WR v (realComponent F (r + 1) v g)) * ∏ w, WC w (complexComponent F (r + 1) w g)
    exact Fintype.prod_sum_type f
  have hInf' : HasPrescribedInfiniteWhittakerProduct
      (infiniteResidual S P' hP' hPS' ψ.complex⁻¹ (fun v => (D v).rightFactor.reference) (PiTensorProduct.tprod ℂ b'))
      κ' WR' WC' := by
    intro g
    have he := hProd'.choose_spec.choose_spec.2.2.2 b' g
    simp only [ψ', complex_inverseCharacter] at he
    refine he.trans ?_
    apply congrArg (fun z : ℂ => κ' * z)
    let f (i : Index F) := M'.model i (b' i) (placeComponents (r + 1) g i)
    change (∏ i, f i) = (∏ v, WR' v (realComponent F (r + 1) v g)) * ∏ w, WC' w (complexComponent F (r + 1) w g)
    exact Fintype.prod_sum_type f
  have hN := exists_ordinaryEqualNormalization_of_pure_product (c := c) (hPS := hPS) (hPS' := hPS')
    hψF hψv D (PiTensorProduct.tprod ℂ b) (PiTensorProduct.tprod ℂ b') WR WR' WC WC' ΦR ΦC ΦS
    (fun _ => realQuotientMeasureData r) (fun _ => complexQuotientMeasureData r) _ _
    hProd.choose_spec.choose_spec.1 hProd'.choose_spec.choose_spec.1 hPairR
    (fun w => ComplexCharacterChange.model_pair_invariant (hWC w) (hWC' w)) hInf hInf' NR NC NS
  have ha : (fun v => (D v).leftFactor.vector) = a := funext hD
  have ha' : (fun v => (D v).rightFactor.vector) = a' := funext hD'
  let I (aLeft : ∀ v : S, P.localFactor v) (aRight : ∀ v : S, P'.localFactor v) :=
    partialEqualWhittakerIntegral F S
      (cuspWhittaker F T ψ.complex (poleEqualPureVector P hP hPS aLeft b))
      (cuspWhittaker F T' ψ.complex⁻¹ (poleEqualPureVector P' hP' hPS' aRight b'))
      (poleEqualSchwartzTensor ΦR ΦC ΦS)
  have he := congrArg₂ I ha ha'
  change Nonempty (OrdinaryIntegralNormalization (I a a') _)
  exact ⟨he ▸ hN.choose_spec.2.choose⟩


theorem exists_ordinaryEqualNormalization_of_pure_tensors_at
    (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (hNReal : RealEqualOrdinaryNormalizedContinuationAt r)
    (hNComplex : ComplexEqualOrdinaryNormalizedContinuationAt r)
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
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (b : ∀ i : Index F, T.placeDensityModels.subspace i)
    (b' : ∀ i : Index F, T'.placeDensityModels.subspace i)
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ) (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1) :
    let x := poleEqualPureVector P hP hPS a b
    let x' := poleEqualPureVector P' hP' hPS' a' b'
    Nonempty (OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') (poleEqualSchwartzTensor ΦR ΦC ΦS))
      (fun s => archimedeanPairProduct dR dR' dC dC' s * ∏ v ∈ S, c.finiteL v s)) :=
  exists_ordinaryEqualNormalization_of_pure_tensors_placewise c hPS hPS' hT hT' hψF hS hψv ν
    (fun _ => hNReal) hNComplex M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC'
    a a' b b' ΦR ΦC ΦS

/-- Normalize the partial integral of any indicated pure equal-rank test using ordinary
local continuation for the specified coefficient models. -/
theorem exists_ordinaryEqualNormalization_of_pure_tensors
    (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (hNReal : RealOrdinaryNormalizedContinuationStatement)
    (hNComplex : ComplexOrdinaryNormalizedContinuationStatement)
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
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (b : ∀ i : Index F, T.placeDensityModels.subspace i)
    (b' : ∀ i : Index F, T'.placeDensityModels.subspace i)
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ) (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1) :
    let x := poleEqualPureVector P hP hPS a b
    let x' := poleEqualPureVector P' hP' hPS' a' b'
    Nonempty (OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') (poleEqualSchwartzTensor ΦR ΦC ΦS))
      (fun s => archimedeanPairProduct dR dR' dC dC' s * ∏ v ∈ S, c.finiteL v s)) :=
  exists_ordinaryEqualNormalization_of_pure_tensors_at c hPS hPS' hT hT' hψF hS hψv ν
    (hNReal.2 r) (hNComplex.2 r) M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC'
    a a' b b' ΦR ΦC ΦS

end Langlands.Global.CuspidalPairPoles
