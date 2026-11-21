import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProduct

/-! # The ranges of compared infinite Whittaker models are the actual restrictions -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

universe u uQ

open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open Automorphic InfinitePlaceFamily CompletionPadic
open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

variable {F : Type u} [Field F] [NumberField F]

local instance actualRangeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance actualRangeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

private theorem placeTuplePoint_update_real (n : ℕ) (v : {v : InfinitePlace F // v.IsReal})
    (g : Langlands.GeneralLinear n ℝ) :
    placeTuplePoint n (Function.update (1 : PlaceTuple (F := F) n) (.inl v) g) =
      realPlacePoint F n v g := by
  apply congrArg (fun p => adelicPoint F n (placeGL F n p) 1)
  apply Prod.ext
  · funext w
    change Function.update (1 : PlaceTuple (F := F) n) (.inl v) g (.inl w) =
      (Pi.mulSingle v g : UnipotentClass.RealGL F n) w
    by_cases h : w = v
    · subst w
      rw [Function.update_self, Pi.mulSingle_eq_same]
    · rw [Function.update_of_ne (Sum.inl_injective.ne h), Pi.mulSingle_eq_of_ne h]
      rfl
  · funext w
    change Function.update (1 : PlaceTuple (F := F) n) (.inl v) g (.inr w) = 1
    rw [Function.update_of_ne (by simp)]
    rfl

private theorem placeTuplePoint_update_complex (n : ℕ) (w : {w : InfinitePlace F // w.IsComplex})
    (g : Langlands.GeneralLinear n ℂ) :
    placeTuplePoint n (Function.update (1 : PlaceTuple (F := F) n) (.inr w) g) =
      complexPlacePoint F n w g := by
  apply congrArg (fun p => adelicPoint F n (placeGL F n p) 1)
  apply Prod.ext
  · funext v
    change Function.update (1 : PlaceTuple (F := F) n) (.inr w) g (.inl v) = 1
    rw [Function.update_of_ne (by simp)]
    rfl
  · funext v
    change Function.update (1 : PlaceTuple (F := F) n) (.inr w) g (.inr v) =
      (Pi.mulSingle w g : UnipotentClass.ComplexGL F n) v
    by_cases h : v = w
    · subst v
      rw [Function.update_self, Pi.mulSingle_eq_same]
    · rw [Function.update_of_ne (Sum.inr_injective.ne h), Pi.mulSingle_eq_of_ne h]
      rfl

private theorem finitePoint_one (n : ℕ) : finitePoint F n 1 = 1 := by
  unfold finitePoint adelicPoint
  rw [map_one]
  change (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofFinite F n 1) = 1
  rw [map_one, map_one]

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {hP : HasIrreducibleAdmissibleComponents P}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {S : Finset (FinitePlace F)}

local instance actualRangeRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance actualRangeContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance actualRangeFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance actualRangeAutomorphicGroup : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance actualRangeStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance actualRangeSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- The range at each place consists of exactly the actual Whittaker restrictions there. -/
def HasActualPlaceWhittakerRanges (M : ModelData P hP ψ.complex) : Prop :=
  (∀ (v : RP) W, W ∈ LinearMap.range (M.model (.inl v)) ↔ IsRealPlaceWhittaker F T ψ.complex v W) ∧
  ∀ (w : CP) W, W ∈ LinearMap.range (M.model (.inr w)) ↔ IsComplexPlaceWhittaker F T ψ.complex w W

private theorem exists_model_as_restriction (M : ModelData P hP ψ.complex)
    (a : FiniteTensor P) (b₀ : ∀ i : Index F, T.placeDensityModels.subspace i)
    (h₀ : ∀ i, M.model i (b₀ i) 1 = 1) (hBase : tensorWhittaker P hP ψ.complex a b₀ 1 ≠ 0)
    (i : Index F) (b : T.placeDensityModels.subspace i) :
    ∃ x : T.Space, ∀ g : PlaceGroup (r + 1) i,
      M.model i b g = cuspWhittaker F T ψ.complex x
        (placeTuplePoint (r + 1) (Function.update (1 : PlaceTuple (F := F) (r + 1)) i g)) := by
  let g₀ : PlaceTuple (F := F) (r + 1) := 1
  let cmp := M.slice a i b₀ g₀
  let c := cmp.choose
  have hc := cmp.choose_spec
  have hu : Function.update b₀ i (b₀ i) = b₀ := Function.update_eq_self_iff.mpr rfl
  have hv : Function.update g₀ i 1 = g₀ := Function.update_eq_self_iff.mpr rfl
  have hBaseEq : tensorWhittaker P hP ψ.complex a b₀ g₀ = c := by
    calc
      _ = tensorWhittaker P hP ψ.complex a (Function.update b₀ i (b₀ i)) (Function.update g₀ i 1) :=
        (congrArg₂ (tensorWhittaker P hP ψ.complex a) hu hv).symm
      _ = c * M.model i (b₀ i) 1 := hc (b₀ i) 1
      _ = c := by rw [h₀, mul_one]
  have hc₀ : c ≠ 0 := hBaseEq ▸ hBase
  let y := P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b₀ i b))
  refine ⟨c⁻¹ • y, fun g => ?_⟩
  let q := placeTuplePoint (r + 1) (Function.update g₀ i g)
  change M.model i b g = cuspWhittaker F T ψ.complex (c⁻¹ • y) q
  calc
    _ = c⁻¹ * (c * M.model i b g) := by rw [← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
    _ = c⁻¹ * tensorWhittaker P hP ψ.complex a (Function.update b₀ i b) (Function.update g₀ i g) :=
      congrArg (fun z : ℂ => c⁻¹ * z) (hc b g).symm
    _ = _ := (UnramifiedWhittaker.cuspWhittaker_smul F ψ.complex T c⁻¹ y q).symm

/-- A normalized comparison identifies each model range with the actual single-place
restrictions. The nonzero normalization scalar supplies the converse inclusion. -/
theorem hasActualPlaceWhittakerRanges (M : ModelData P hP ψ.complex)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hPS : P.exceptional ⊆ S) (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1) :
    HasActualPlaceWhittakerRanges M := by
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  have hProd := exists_normalized_product (P := P) (hP := hP) ψ hψ S hPS hS ψv hψv ℓ a₀ ha₀ M
  let b₀ := hProd.choose
  have h₀ := hProd.choose_spec.choose_spec.2.1
  have hBase := hProd.choose_spec.choose_spec.2.2.1 ▸ hProd.choose_spec.choose_spec.1
  have hLift := exists_model_as_restriction M (P.finitePure S hPS a₀) b₀ h₀ hBase
  constructor
  · intro v W
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨x, hx⟩ := hLift (.inl v) b
      refine ⟨x, 1, funext fun g => ?_⟩
      simpa only [placeTuplePoint_update_real, finitePoint_one, mul_one] using hx g
    · intro h
      exact LinearMap.mem_range.mpr (exists_model_real M hχ v W h)
  · intro w W
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨x, hx⟩ := hLift (.inr w) b
      refine ⟨x, 1, funext fun g => ?_⟩
      simpa only [placeTuplePoint_update_complex, finitePoint_one, mul_one] using hx g
    · intro h
      exact LinearMap.mem_range.mpr (exists_model_complex M hχ w W h)

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
