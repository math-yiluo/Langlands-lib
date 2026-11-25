import Langlands.Global.RankinSelberg.UnequalInfiniteWhittakerReduction
import Langlands.Global.RankinSelberg.UnequalInfinitePlaceTests
import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction

/-! # Unequal-rank pointwise factorization from slice comparisons and place tests -/

noncomputable section
open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic InfinitePlaceFamily
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.Global.HeckeFunctionalEquation
open Langlands.LocalFactor.Archimedean
open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual InfiniteWhittakerSlice

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance unequalSliceSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalSliceSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

private theorem product_ne_zero_above {F : Type u} [Field F] [NumberField F]
    (fR : (RP F) → ℂ → ℂ) (fC : (CP F) → ℂ → ℂ)
    (hR : ∀ v, HolomorphicNonzeroOnRightHalfPlane (fR v))
    (hC : ∀ w, HolomorphicNonzeroOnRightHalfPlane (fC w)) (a : ℝ) :
    ∃ s : ℂ, a < s.re ∧ ((∏ v, fR v s) * ∏ w, fC w s) ≠ 0 := by
  let f : Index F → ℂ → ℂ := Sum.elim fR fC
  have hf : ∀ i, HolomorphicNonzeroOnRightHalfPlane (f i) :=
    fun i => match i with | .inl v => hR v | .inr w => hC w
  have hp := HolomorphicNonzeroOnRightHalfPlane.finset_prod Finset.univ f hf
  obtain ⟨s, hs, hne⟩ := hp.exists_ne_zero_above a
  refine ⟨s, hs, ?_⟩
  simpa only [Fintype.prod_sum_type, f, Sum.elim_inl, Sum.elim_inr] using hne

/-- With the comparison model, any prescribed family of actual place restrictions occurs as a
normalized product. This is the single-presentation step, at either rank. -/
theorem InfiniteWhittakerSlice.exists_normalized_product_of_restrictions
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {n : ℕ} {T : CuspidalOperatorRealization F n}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (hI : HasIrreducibleAdmissibleComponents P)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (M : ModelData P hI ψ.complex)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (WR : (RP F) → Langlands.GeneralLinear (n + 1) ℝ → ℂ)
    (WC : (CP F) → Langlands.GeneralLinear (n + 1) ℂ → ℂ)
    (hR : ∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v))
    (hC : ∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)) :
    ∃ (τ : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) (κ : ℂ), κ ≠ 0 ∧
      ∀ g : Points F (n + 1), infiniteResidual S P hI hPS ψ.complex a₀ τ g =
        κ * ((∏ v, WR v (realComponent F (n + 1) v g)) *
          ∏ w, WC w (complexComponent F (n + 1) w g)) := by
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  choose bR hbR using fun v : RP F => exists_model_real M hχ v (WR v) (hR v)
  choose bC hbC using fun w : CP F => exists_model_complex M hχ w (WC w) (hC w)
  let b (i : Index F) : T.placeDensityModels.subspace i := match i with
    | .inl v => bR v
    | .inr w => bC w
  obtain ⟨_, κ, hκ, _, _, hprod⟩ :=
    exists_normalized_product (P := P) (hP := hI) ψ hψ S hPS hS ψv hψv ℓ a₀ ha₀ M
  refine ⟨PiTensorProduct.tprod ℂ b, κ, hκ, fun g => (hprod b g).trans ?_⟩
  apply congrArg (fun z : ℂ => κ * z)
  let f (i : Index F) := M.model i (b i) (placeComponents (n + 1) g i)
  change (∏ i, f i) = _
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (fun x y : ℂ => x * y)
    (Finset.prod_congr rfl (fun v _ => congrFun (hbR v) (realComponent F (n + 1) v g)))
    (Finset.prod_congr rfl (fun w _ => congrFun (hbC w) (complexComponent F (n + 1) w g)))

/-- At a fixed field and pair of presentations, assemble the joint test from two supplied
slice comparisons and independent test witnesses at the places that actually occur. -/
theorem unequalInfiniteWhittakerTest_of_placeData
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r t : ℕ} (h : t < r) {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hI : HasIrreducibleAdmissibleComponents P) (hI' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hsupp : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (aR : (RP F) → ℝˣ) (aC : (CP F) → ℂˣ)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, FactorFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (a₀ : ∀ v : S, P.localFactor v) (a₀' : ∀ v : S, P'.localFactor v)
    (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1) (ha₀' : ∀ v : S, (ℓ' v).val (a₀' v) = 1)
    (M : ModelData P hI ψ.complex) (M' : ModelData P' hI' ψ.complex⁻¹)
    (hR : ∀ v, HasRealUnequalPlaceTest h T T' ψ v (aR v))
    (hC : ∀ w, HasComplexUnequalPlaceTest h T T' ψ w (aC w)) :
    ∃ (τ : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
      (τ' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
      (I : UnequalInfiniteTestData h T T' ψ aR aC),
      (∀ g : Points F (r + 1),
        infiniteResidual S P hI hPS ψ.complex a₀ τ g =
          I.κ * ((∏ v, I.WR v (realComponent F (r + 1) v g)) *
            ∏ w, I.WC w (complexComponent F (r + 1) w g))) ∧
      ∀ g : Points F (t + 1),
        infiniteResidual S P' hI' hPS' ψ.complex⁻¹ a₀' τ' g =
          I.κ' * ((∏ v, I.WR' v (realComponent F (t + 1) v g)) *
            ∏ w, I.WC' w (complexComponent F (t + 1) w g)) := by
  simp only [HasRealUnequalPlaceTest] at hR
  simp only [HasComplexUnequalPlaceTest] at hC
  choose WR WR' DR hWR hWR' hoR hdR using hR
  choose WC WC' DC hWC hWC' hoC hdC using hC
  obtain ⟨τ, κ, hκ, hprod⟩ := exists_normalized_product_of_restrictions P hI ψ hψ S hPS hsupp
    M ψv hψv ℓ a₀ ha₀ WR WC hWR hWC
  let ψ' := inverseCharacter ψ
  have hψ' := inverseCharacter_rational ψ hψ
  have hχ' : ψ'.complex = ψ.complex⁻¹ := complex_inverseCharacter ψ
  have M₁ : ModelData P' hI' ψ'.complex := by rw [hχ']; exact M'
  have hR₁ (v : RP F) : IsRealPlaceWhittaker F T' ψ'.complex v (WR' v) := hχ'.symm ▸ hWR' v
  have hC₁ (w : CP F) : IsComplexPlaceWhittaker F T' ψ'.complex w (WC' w) := hχ'.symm ▸ hWC' w
  obtain ⟨τ', κ', hκ', hprod'⟩ := exists_normalized_product_of_restrictions P' hI' ψ' hψ' S hPS'
    (finiteAdditiveSupport_inverseCharacter ψ S hsupp) M₁ (fun v => inverseFinite v.1 (ψv v))
    (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v)) ℓ' a₀' ha₀' WR' WC' hR₁ hC₁
  let I : UnequalInfiniteTestData h T T' ψ aR aC :=
    ⟨κ, κ', hκ, hκ', WR, WR', WC, WC', hWR, hWR', hWC, hWC', DR, DC,
      product_ne_zero_above _ _ hoR hoC, product_ne_zero_above _ _ hdR hdC⟩
  refine ⟨τ, τ', I, hprod, ?_⟩
  simpa only [hχ'] using hprod'

/-- The single-presentation comparison and the two place assertions imply the joint infinite
test for all the data of the pointwise theorem. -/
theorem unequalInfiniteWhittakerTest_of_local
    (hModels : InfiniteWhittakerSliceModelStatement.{u, uQ})
    (hReal : RealUnequalPlaceTestsStatement.{u}) (hComplex : ComplexUnequalPlaceTestsStatement.{u}) :
    UnequalInfiniteWhittakerTestStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hPS' hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    ψv hψv ℓ ℓ' a₀ a₀' ha₀ ha₀'
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  obtain ⟨M⟩ := hModels F r T P hI ψ.complex hχ dR hdR dC hdC
  let ψ' := inverseCharacter ψ
  have hχ' := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ' (inverseCharacter_rational ψ hψ)
  obtain ⟨M'⟩ := hModels F t T' P' hI' ψ'.complex hχ' dR' hdR' dC' hdC'
  exact unequalInfiniteWhittakerTest_of_placeData ψ hψ h P P' hI hI' S hPS hPS' hsupp
    aR aC ψv hψv ℓ ℓ' a₀ a₀' ha₀ ha₀' M
    (by simpa only [ψ', complex_inverseCharacter] using M')
    (fun v => hReal F ψ hψ r t h T Td T' Td' hTd hTd' v (aR v) (haR v)
      (dR v) (dR' v) (dRd v) (dRd' v) (hdR v) (hdR' v) (hdRd v) (hdRd' v))
    (fun w => hComplex F ψ hψ r t h T Td T' Td' hTd hTd' w (aC w) (haC w)
      (dC w) (dC' w) (dCd w) (dCd' w) (hdC w) (hdC' w) (hdCd w) (hdCd' w))

/-- The remaining three inputs for the exact unequal-rank pointwise factorization. -/
def UnequalInfiniteWhittakerSliceReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} →
    RealUnequalPlaceTestsStatement.{u} → ComplexUnequalPlaceTestsStatement.{u} →
    UnequalPointwiseFactorizationStatement.{u, uQ}

/-- Assemble the archimedean input and use the pointwise product theorem. -/
theorem unequalInfiniteWhittakerSliceReduction : UnequalInfiniteWhittakerSliceReductionStatement.{u, uQ} :=
  fun hModels hReal hComplex =>
    unequalPointwiseOfInfiniteTests (unequalInfiniteWhittakerTest_of_local hModels hReal hComplex)

end Langlands.Global.RankinSelbergGlobal
