import Langlands.Automorphic.CuspidalPlaceTensorSlice
import Langlands.Global.Factors.CuspidalBlockStandardCoefficients
import Langlands.Global.RankinSelberg.ArchimedeanActualWhittakerIntertwiners
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne
import Langlands.Global.RankinSelberg.ComplexPlaceFrozenWhittaker
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceModelTCStatement

/-! # The normalized infinite Whittaker slices over a totally complex field -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic InfinitePlaceFamily InfiniteWhittakerSlice
open LocalFactor.Archimedean CuspidalPairFunctionalEquation HeckeFunctionalEquation
open Langlands.Archimedean (complexStandardRep complexStandardLie)

attribute [local instance 100] LieRing.ofAssociativeRing

local instance complexSliceRationalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance complexSliceContinuousGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance complexSliceSmoothGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance complexSliceFormsGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance complexSliceStableGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance complexSliceRealizationGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}
local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}

section TensorGeometry

variable {F : Type u} [Field F] [NumberField F]

omit [NumberField F] in
private theorem complexPlaceGL_eq (n : ℕ) (w : CP F) (k : GeneralLinear n ℂ) :
    complexPlaceGL F n w k = placeGL F n (1, Pi.mulSingle w k) := rfl

private theorem frozenTuple (n : ℕ) (w : CP F) (g : PlaceTuple (F := F) n)
    (k : GeneralLinear n ℂ) :
    let q := placeGL F n ((fun v => g (.inl v)), (fun v => Function.update g (.inr w) 1 (.inr v)))
    placeTuplePoint n (Function.update g (.inr w) k) =
      adelicPoint F n (q * complexPlaceGL F n w k) 1 := by
  dsimp only [placeTuplePoint]
  rw [complexPlaceGL_eq, ← map_mul]
  apply congrArg (fun p => adelicPoint F n (placeGL F n p) 1)
  apply Prod.ext
  · funext v
    change Function.update g (.inr w) k (.inl v) = g (.inl v) * 1
    rw [Function.update_of_ne (by simp), mul_one]
  · funext v
    change Function.update g (.inr w) k (.inr v) =
      Function.update g (.inr w) 1 (.inr v) * (Pi.mulSingle w k : (CP F) → GeneralLinear n ℂ) v
    by_cases hv : v = w
    · subst v
      rw [Function.update_self, Function.update_self, Pi.mulSingle_eq_same, one_mul]
    · rw [Function.update_of_ne (Sum.inr_injective.ne hv),
        Function.update_of_ne (Sum.inr_injective.ne hv), Pi.mulSingle_eq_of_ne hv, mul_one]

private theorem frozenTuple_commute (n : ℕ) (w : CP F) (g : PlaceTuple (F := F) n)
    (k : GeneralLinear n ℂ) :
    Commute (complexPlaceGL F n w k)
      (placeGL F n ((fun v => g (.inl v)), (fun v => Function.update g (.inr w) 1 (.inr v)))) := by
  rw [complexPlaceGL_eq]
  apply Commute.map
  let p : ((RP F) → GeneralLinear n ℝ) × ((CP F) → GeneralLinear n ℂ) := (1, Pi.mulSingle w k)
  change p * _ = _ * p
  apply Prod.ext
  · funext v
    change 1 * g (.inl v) = g (.inl v) * 1
    rw [one_mul, mul_one]
  · funext v
    change (Pi.mulSingle w k : (CP F) → GeneralLinear n ℂ) v * Function.update g (.inr w) 1 (.inr v) =
      Function.update g (.inr w) 1 (.inr v) * (Pi.mulSingle w k : (CP F) → GeneralLinear n ℂ) v
    by_cases hv : v = w
    · subst v
      rw [Function.update_self, one_mul, mul_one]
    · rw [Pi.mulSingle_eq_of_ne hv, one_mul, mul_one]

end TensorGeometry

section SliceMap

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

local instance sliceDensityGroup (i : Index F) : AddCommGroup (T.placeDensityModels.subspace i) :=
  Submodule.addCommGroup _

private theorem tensorSlice_isComplexPlaceMap
    (w : CP F) {d : List ComplexCharacterData} (hd : T.realization.HasComplexPlaceParameter w d)
    (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ j, T.placeDensityModels.subspace j) :
    T.realization.IsComplexPlaceMap w d ((T.placeTensorSlice (.inr w) a b).comp
      (CuspidalBlockInduction.complexStandardCoefficientEquiv T w hd).toLinearEquiv.toLinearMap) := by
  let e := CuspidalBlockInduction.complexStandardCoefficientEquiv T w hd
  let L := T.placeTensorSlice (.inr w) a b
  let D := T.placeDensityModels
  let A := T.finiteInfiniteDecomposition
  obtain ⟨_, _, _, hStdK, hStdL⟩ := hd
  constructor
  · intro k f
    let l : Matrix.unitaryGroup (Fin (r + 1)) ℂ := ⟨(k.val : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), k.2⟩
    have hf := (hStdK k f).1
    have hl : Unitary.toUnits l = k.val := Units.ext rfl
    have he : ⟨_, hf⟩ = complexStandardRep (r + 1) d l f := by
      apply Subtype.ext
      rw [Archimedean.principalSeriesRep_apply_coe, hl]
    refine ⟨hf, ?_⟩
    change L (e ⟨_, hf⟩) = T.realization.complexPlaceCompactRepresentation w l (L (e f))
    have hK : e (complexStandardRep (r + 1) d l f) = D.sourceCompact (.inr w) l (e f) :=
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' (FreeMonoid.of (Sum.inl l))) f
    exact (congrArg (fun x => L (e x)) he).trans ((congrArg L hK).trans
      (D.tensorSlice_compact A.finite T.irreducible A.nonzero A.irreducible A.admissible
        (.inr w) a b l (e f)))
  · intro X f
    have hf := (hStdL X f).1
    have he : ⟨_, hf⟩ = complexStandardLie (r + 1) d (1 ⊗ₜ[ℝ] X) f :=
      Subtype.ext (Archimedean.principalSeriesLie_one_tmul_apply_coe _ _ _ X f).symm
    refine ⟨hf, ?_⟩
    change L (e ⟨_, hf⟩) = T.realization.complexPlaceLieAction w (1 ⊗ₜ[ℝ] X) (L (e f))
    have hLie : e (complexStandardLie (r + 1) d (1 ⊗ₜ[ℝ] X) f) =
        D.sourceLie (.inr w) (1 ⊗ₜ[ℝ] X) (e f) :=
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' (FreeMonoid.of (Sum.inr (1 ⊗ₜ[ℝ] X)))) f
    exact (congrArg (fun x => L (e x)) he).trans ((congrArg L hLie).trans
      (D.tensorSlice_lie A.finite T.irreducible A.nonzero A.irreducible A.admissible
        (.inr w) a b (1 ⊗ₜ[ℝ] X) (e f)))

end SliceMap

/-- The actual normalized infinite slice model over a totally complex field has the
full coefficient range of each supplied complex standard module. -/
def InfiniteWhittakerComplexSliceDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u,uQ} T) (hP : HasIrreducibleAdmissibleComponents P)
    (aC : (CP F) → ℂˣ), (∀ w, IsComplexAdditiveComponent ψ w.1 w.2 (aC w)) →
  ∀ (dC : (CP F) → List ComplexCharacterData), (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    ∃ M : ModelData P hP ψ.complex,
      ∀ w : CP F, LinearMap.range (M.model (.inr w)) = complexWhittakerModel r (dC w) (aC w)

theorem infiniteWhittakerComplexSliceData : InfiniteWhittakerComplexSliceDataStatement.{u,uQ} := by
  intro F _ _ _ _ ψ hψ r T P hP aC haC dC hdC
  let : IsEmpty (RP F) :=
    ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex v.1) v.2⟩
  obtain ⟨B, hB, hRef⟩ :
      ∃ B : ∀ w : CP F, complexStandardKFinite (r + 1) (dC w) →ₗ[ℂ] (GeneralLinear (r + 1) ℂ → ℂ),
        (∀ w, IsComplexWhittakerIntertwiner r (dC w) (aC w) (B w)) ∧
        ∀ w, ∃ f, B w f 1 = 1 := by
    have h (w : CP F) :=
      (archimedeanActualWhittakerIntertwiners F ψ hψ r T).2 w (dC w) (hdC w) (aC w) (haC w)
    have h' (w : CP F) : ∃ B : complexStandardKFinite (r + 1) (dC w) →ₗ[ℂ]
        (GeneralLinear (r + 1) ℂ → ℂ), IsComplexWhittakerIntertwiner r (dC w) (aC w) B ∧ ∃ f, B f 1 = 1 := by
      obtain ⟨_, B, _, hB, hRef, _⟩ := h w
      exact ⟨B, hB, hRef⟩
    choose B hB hRef using h'
    exact ⟨B, hB, hRef⟩
  have hB0 (w : CP F) : B w ≠ 0 := by
    obtain ⟨f, hf⟩ := hRef w
    intro h
    rw [h] at hf
    exact zero_ne_one hf
  let e (w : CP F) := (CuspidalBlockInduction.complexStandardCoefficientEquiv T w (hdC w)).toLinearEquiv
  let model (i : Index F) : T.placeDensityModels.subspace i →ₗ[ℂ] (PlaceGroup (r + 1) i → ℂ) :=
    match i with
    | .inl v => isEmptyElim v
    | .inr w => (B w).comp (e w).symm.toLinearMap
  have hNorm (i : Index F) : ∃ b, model i b 1 = 1 := by
    cases i with
    | inl v => exact isEmptyElim v
    | inr w =>
      obtain ⟨f, hf⟩ := hRef w
      exact ⟨e w f, (congrArg (fun x => B w x 1) ((e w).symm_apply_apply f)).trans hf⟩
  have hSliced (x : FiniteTensor P) (i : Index F)
      (b : ∀ j, T.placeDensityModels.subspace j) (g : PlaceTuple (F := F) (r + 1)) :
      ∃ c : ℂ, ∀ v : T.placeDensityModels.subspace i, ∀ k : PlaceGroup (r + 1) i,
        tensorWhittaker P hP ψ.complex x (Function.update b i v) (Function.update g i k) =
          c * model i v k := by
    cases i with
    | inl v => exact isEmptyElim v
    | inr w =>
      let a := P.finiteTensorEquiv hP x
      let L := (T.placeTensorSlice (.inr w) a b).comp (e w).toLinearMap
      let q := placeGL F (r + 1)
        ((fun v => g (.inl v)), (fun v => Function.update g (.inr w) 1 (.inr v)))
      have hL : T.realization.IsComplexPlaceMap w (dC w) L :=
        tensorSlice_isComplexPlaceMap T w (hdC w) a b
      obtain ⟨B', hB', hValue⟩ := complexPlaceFrozenWhittaker F ψ.complex
        (isStandardAdditiveCharacter_of_unitary ψ hψ) r T w (aC w)
        (complexComponent_complex ψ w (aC w) (haC w)) q (frozenTuple_commute (r + 1) w g)
        (dC w) L hL
      obtain ⟨c, hc⟩ := ComplexJacquetMultiplicityOne.exactIntertwiner_proportional r
        (dC w) (aC w) B' (B w) hB' (hB w) (hB0 w)
      refine ⟨c, fun v k => ?_⟩
      change cuspWhittaker F T ψ.complex
        (T.placeTensorSlice (.inr w) a b v) (placeTuplePoint (r + 1) (Function.update g (.inr w) k)) =
          c * B w ((e w).symm v) k
      rw [frozenTuple (r + 1) w g k]
      have hLv : L ((e w).symm v) = T.placeTensorSlice (.inr w) a b v :=
        congrArg (T.placeTensorSlice (.inr w) a b) ((e w).apply_symm_apply v)
      exact (congrArg (fun z => cuspWhittaker F T ψ.complex z
        (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w k) 1)) hLv.symm).trans
        ((hValue ((e w).symm v) k).symm.trans
          (congrArg (fun M : complexStandardKFinite (r + 1) (dC w) →ₗ[ℂ]
            (GeneralLinear (r + 1) ℂ → ℂ) => M ((e w).symm v) k) hc))
  refine ⟨⟨model, hNorm, hSliced⟩, fun w => ?_⟩
  change LinearMap.range ((B w).comp (e w).symm.toLinearMap) = _
  rw [ComplexJacquetMultiplicityOne.model_eq_range_of_nonzero r (dC w) (aC w) (B w) (hB w) (hB0 w)]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨(e w).symm v, rfl⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨e w f, congrArg (B w) ((e w).symm_apply_apply f)⟩

end Langlands.Global.RankinSelbergGlobal
