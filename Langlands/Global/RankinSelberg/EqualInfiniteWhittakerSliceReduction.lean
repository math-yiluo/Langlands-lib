import Langlands.Global.RankinSelberg.EqualInfinitePlaceTests
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProduct

/-! # Equal-rank factorization from local Whittaker comparisons and tests -/

noncomputable section
open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic InfinitePlaceFamily
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.LocalFactor.Archimedean
open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual InfiniteWhittakerSlice

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The archimedean Whittaker comparison for one actual cuspidal tensor presentation.
The local maps have a nonzero identity value and their lines contain all actual slices. -/
def InfiniteWhittakerSliceModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hI : HasIrreducibleAdmissibleComponents P)
    (χ : AddChar (Adeles F) ℂ),
    IsStandardAdditiveCharacter F χ →
  ∀ (dR : (RP F) → List RealBlock),
    (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
  ∀ (dC : (CP F) → List ComplexCharacterData),
    (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    Nonempty (ModelData P hI χ)

section Realization

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u, uQ} T) (hI : HasIrreducibleAdmissibleComponents P)
  (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
  (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
  (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
  (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)

include hψ hS in
/-- Arbitrary supplied actual place restrictions can be prescribed simultaneously for
the normalized infinite residual when the model comparison is given. -/
private theorem exists_infiniteTensor_for_restrictions
    (M : ModelData P hI ψ.complex)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (WR : (RP F) → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (WC : (CP F) → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (hR : ∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v))
    (hC : ∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)) :
    ∃ (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) (κ : ℂ), κ ≠ 0 ∧
      ∀ g : Points F (r + 1), infiniteResidual S P hI hPS ψ.complex a₀ t g =
        κ * ((∏ v, WR v (realComponent F (r + 1) v g)) *
          ∏ w, WC w (complexComponent F (r + 1) w g)) := by
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
  let f (i : Index F) := M.model i (b i) (placeComponents (r + 1) g i)
  change (∏ i, f i) = _
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (fun x y : ℂ => x * y)
    (Finset.prod_congr rfl (fun v _ => congrFun (hbR v) (realComponent F (r + 1) v g)))
    (Finset.prod_congr rfl (fun w _ => congrFun (hbC w) (complexComponent F (r + 1) w g)))

end Realization

private theorem mul_products {A B : Type*} [Fintype A] [Fintype B] (κ κ' : ℂ)
    (f f' : A → ℂ) (g g' : B → ℂ) :
    (κ * ((∏ i, f i) * ∏ j, g j)) * (κ' * ((∏ i, f' i) * ∏ j, g' j)) =
      κ * κ' * ((∏ i, f i * f' i) * ∏ j, g j * g' j) := by
  simp only [Finset.prod_mul_distrib]
  ac_rfl

set_option maxHeartbeats 6000000 in
/-- Local slice comparisons and independent local tests supply the joint infinite
premise of the equal-rank reduction. -/
theorem equalInfiniteWhittakerTest_of_local
    (hModels : InfiniteWhittakerSliceModelStatement.{u, uQ})
    (hReal : RealEqualPlaceTestsStatement.{u}) (hComplex : ComplexEqualPlaceTestsStatement.{u}) :
    EqualInfiniteWhittakerTestStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r T Td T' Td' hTd hTd' P P' hI hI' S hPS hPS' hS aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    ψv hψv ℓ ℓ' a₀ a₀' ha₀ ha₀'
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  obtain ⟨M⟩ := hModels F r T P hI ψ.complex hχ dR hdR dC hdC
  let ψ' := inverseCharacter ψ
  have hψ' (x : F) : ψ' (algebraMap F (Adeles F) x) = 1 := by
    change inverseCharacter ψ (algebraMap F (Adeles F) x) = 1
    rw [inverseCharacter_apply, hψ, inv_one]
  have hχ' := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ' hψ'
  obtain ⟨M'⟩ := hModels F r T' P' hI' ψ'.complex hχ' dR' hdR' dC' hdC'
  obtain ⟨I⟩ := infiniteTestData_of_local (aR := aR) (aC := aC)
    (fun v => hReal F ψ hψ r T Td T' Td' hTd hTd' v (aR v) (haR v)
      (dR v) (dR' v) (dRd v) (dRd' v) (hdR v) (hdR' v) (hdRd v) (hdRd' v))
    (fun w => hComplex F ψ hψ r T Td T' Td' hTd hTd' w (aC w) (haC w)
      (dC w) (dC' w) (dCd w) (dCd' w) (hdC w) (hdC' w) (hdCd w) (hdCd' w))
  obtain ⟨t, κ, hκ, hprod⟩ := exists_infiniteTensor_for_restrictions P hI ψ hψ S hPS hS
    M ψv hψv ℓ a₀ ha₀ I.WR I.WC I.isWR I.isWC
  have hR' (v : RP F) : IsRealPlaceWhittaker F T' ψ'.complex v (I.WR' v) := by
    simpa only [ψ', complex_inverseCharacter] using I.isWR' v
  have hC' (w : CP F) : IsComplexPlaceWhittaker F T' ψ'.complex w (I.WC' w) := by
    simpa only [ψ', complex_inverseCharacter] using I.isWC' w
  obtain ⟨t', κ', hκ', hprod'⟩ := exists_infiniteTensor_for_restrictions P' hI' ψ' hψ' S hPS'
    (finiteAdditiveSupport_inverseCharacter ψ S hS) M' (fun v => inverseFinite v.1 (ψv v))
    (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v)) ℓ' a₀' ha₀' I.WR' I.WC' hR' hC'
  let J : EqualInfiniteTestData T T' ψ aR aC := { I with
    κ := κ * κ'
    κ_ne_zero := mul_ne_zero hκ hκ' }
  refine ⟨t, t', J, fun g _ => ?_⟩
  have hp' := hprod' g
  simp only [ψ', complex_inverseCharacter] at hp'
  exact (congrArg₂ (fun x y : ℂ => x * y) (hprod g) hp').trans
    (mul_products κ κ'
      (fun v => I.WR v (realComponent F (r + 1) v g)) (fun v => I.WR' v (realComponent F (r + 1) v g))
      (fun w => I.WC w (complexComponent F (r + 1) w g)) (fun w => I.WC' w (complexComponent F (r + 1) w g)))

/-- The only inputs are the single-representation slice comparison and the two
local equal-rank archimedean test assertions. -/
def EqualInfiniteWhittakerSliceReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} →
    RealEqualPlaceTestsStatement.{u} → ComplexEqualPlaceTestsStatement.{u} →
    EqualArchimedeanFactorizationStatement.{u, uQ}

/-- Apply the equal-rank reduction to the assembled infinite data. -/
theorem equalInfiniteWhittakerSliceReduction : EqualInfiniteWhittakerSliceReductionStatement.{u, uQ} :=
  fun hModels hReal hComplex =>
    equalInfiniteWhittakerReduction (equalInfiniteWhittakerTest_of_local hModels hReal hComplex)

end Langlands.Global.RankinSelbergGlobal
