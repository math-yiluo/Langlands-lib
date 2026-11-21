import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProduct
import Langlands.Global.RankinSelberg.RealRankZeroPlace
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.EqualUnfoldingCusp
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-! # The infinite Whittaker slice model in rank one -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open Automorphic InfinitePlaceFamily EqualUnfolding CuspidalPairFunctionalEquation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance rankOneSliceAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance rankOneSliceSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance rankOneSliceRational (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance rankOneSliceContinuous (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance rankOneSliceFiniteSmooth (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance rankOneSliceAutomorphic (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance rankOneSliceStable (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance rankOneSliceSpace {r : ℕ} (T : CuspidalOperatorRealization F r) : AddCommGroup T.Space :=
  Submodule.addCommGroup _
local instance rankOneSlicePlace {r : ℕ} (T : CuspidalOperatorRealization F r) (i : Index F) :
    AddCommGroup (T.placeDensityModels.subspace i) := Submodule.addCommGroup _

omit [CompactSpace (AdeleQuotient F)] in
private theorem scalarPoint_surjective_rankOne : Function.Surjective (scalarPoint F 0) := by
  intro g
  refine exists_scalarPoint_eq F 0 (Subgroup.mem_center_iff.mpr (fun h => ?_))
  apply (GeneralLinearGroupPoints.adelicEquiv F 1).injective
  rw [map_mul, map_mul, RealRankZero.gl_fin_one_mul_comm]

private def evalAtOne (T : CuspidalOperatorRealization F 0) : T.Space →ₗ[ℂ] ℂ :=
  (LinearMap.proj 1).comp (Unfolding.cuspLinear F T)

private theorem evalAtOne_injective (T : CuspidalOperatorRealization F 0)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω) :
    Function.Injective (evalAtOne T) := by
  intro x y he
  apply Unfolding.cuspLinear_injective F T
  funext q
  obtain ⟨z, rfl⟩ := scalarPoint_surjective_rankOne q
  change cuspFunction F T x (scalarPoint F 0 z) = cuspFunction F T y (scalarPoint F 0 z)
  rw [← mul_one (scalarPoint F 0 z), cuspFunction_scalarPoint_mul F T hω,
    cuspFunction_scalarPoint_mul F T hω]
  exact congrArg (_ * ·) he

private theorem cuspFunction_mul_rankOne (T : CuspidalOperatorRealization F 0)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    {x₀ : T.Space} (h₀ : evalAtOne T x₀ = 1) (x : T.Space) (p q : Points F 1) :
    cuspFunction F T x (p * q) = cuspFunction F T x₀ p * cuspFunction F T x q := by
  obtain ⟨z, rfl⟩ := scalarPoint_surjective_rankOne p
  rw [cuspFunction_scalarPoint_mul F T hω, ← mul_one (scalarPoint F 0 z),
    cuspFunction_scalarPoint_mul F T hω]
  change cuspFunction F T x₀ 1 = 1 at h₀
  rw [h₀, mul_one]

omit [CompactSpace (AdeleQuotient F)] in
private theorem placeTuplePoint_one_rankOne : placeTuplePoint 1 (1 : PlaceTuple (F := F) 1) = 1 := by
  have hpair : AdelicGL.pair F 1 1 1 = 1 := by
    apply AdelicGL.ext_infinite_finite F 1 <;> simp
  change (GeneralLinearGroupPoints.adelicEquiv F 1).symm
    (AdelicGL.pair F 1 ((archimedeanGLCoordinates F 1).symm (placeGL F 1 1)) 1) = 1
  rw [map_one, map_one, hpair, map_one]

omit [CompactSpace (AdeleQuotient F)] in
private theorem placeTuplePoint_update_rankOne (i : Index F) (g : PlaceTuple 1) (h : PlaceGroup 1 i) :
    placeTuplePoint 1 (Function.update g i h) =
      placeTuplePoint 1 (Function.update (1 : PlaceTuple 1) i h) *
        placeTuplePoint 1 (Function.update g i 1) := by
  unfold placeTuplePoint
  rw [← adelicPoint_mul, one_mul, ← map_mul]
  congr 1
  apply congrArg (placeGL F 1)
  apply Prod.ext
  · funext w
    by_cases he : Sum.inl w = i
    · subst i
      simp
    · simp [Function.update_of_ne he]
  · funext w
    by_cases he : Sum.inr w = i
    · subst i
      simp
    · simp [Function.update_of_ne he]

/-- Every actual cuspidal tensor presentation in rank one has a normalized
infinite model for its Whittaker slices. -/
def RankOneWhittakerSliceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F 0) (P : CuspidalSpectralPresentation.{u,uQ} T)
    (hP : HasIrreducibleAdmissibleComponents P) (χ : AddChar (Adeles F) ℂ),
    Nonempty (ModelData P hP χ)

set_option maxHeartbeats 5000000 in
theorem rankOneWhittakerSlice : RankOneWhittakerSliceStatement.{u,uQ} := by
  intro F _ _ _ T P hP χ
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  let evalGlobal := evalAtOne T
  have hEvalGlobal := evalAtOne_injective T hω
  let evalLocal (i : Index F) : T.placeDensityModels.subspace i →ₗ[ℂ] ℂ :=
    evalGlobal.comp (T.placeDensityModels.subspace i).subtype
  have hEvalLocal (i : Index F) : Function.Injective (evalLocal i) :=
    hEvalGlobal.comp Subtype.val_injective
  have hRef (i : Index F) : ∃ b : T.placeDensityModels.subspace i, evalLocal i b = 1 := by
    obtain ⟨b, hb, hb'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (T.placeDensityModels.irreducible i).1
    let v : T.placeDensityModels.subspace i := ⟨b, hb⟩
    have hv : evalLocal i v ≠ 0 := fun h =>
      hb' (congrArg Subtype.val (hEvalLocal i (h.trans (map_zero _).symm)))
    exact ⟨(evalLocal i v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  choose b₀ hb₀ using hRef
  obtain ⟨x₀, hx₀⟩ : ∃ x : T.Space, evalGlobal x = 1 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : T.Space)
    have h : evalGlobal x ≠ 0 := fun h => hx (hEvalGlobal (h.trans (map_zero _).symm))
    exact ⟨(evalGlobal x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]⟩
  let q₀ (i : Index F) (h : PlaceGroup 1 i) :=
    placeTuplePoint 1 (Function.update (1 : PlaceTuple 1) i h)
  let C (i : Index F) (h : PlaceGroup 1 i) := cuspFunction F T x₀ (q₀ i h)
  refine ⟨⟨fun i => (evalLocal i).smulRight (C i), fun i => ⟨b₀ i, ?_⟩, ?_⟩⟩
  · change evalLocal i (b₀ i) * cuspFunction F T x₀ (q₀ i 1) = 1
    have hq : q₀ i 1 = 1 := by
      dsimp [q₀]
      rw [show Function.update (1 : PlaceTuple (F := F) 1) i 1 = 1 from
        Function.update_eq_self_iff.mpr rfl, placeTuplePoint_one_rankOne]
    rw [hb₀, hq, one_mul]
    exact hx₀
  · intro a i b g
    refine ⟨tensorWhittaker P hP χ a (Function.update b i (b₀ i)) (Function.update g i 1), ?_⟩
    intro v h
    let x := P.allPlaceTensorEquiv hP
      (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i (b₀ i)))
    have hv : v = (evalLocal i v) • b₀ i := by
      apply hEvalLocal i
      rw [(evalLocal i).map_smul, hb₀ i, smul_eq_mul, mul_one]
    have hx : P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i v)) =
        evalLocal i v • x := by
      have hProd : PiTensorProduct.tprod ℂ (Function.update b i v) =
          (evalLocal i v) • PiTensorProduct.tprod ℂ (Function.update b i (b₀ i)) :=
        (congrArg (fun w => PiTensorProduct.tprod ℂ (Function.update b i w)) hv).trans
          ((PiTensorProduct.tprod ℂ).map_update_smul b i (evalLocal i v) (b₀ i))
      let embed := P.allPlaceTensorEquiv hP
      let y := PiTensorProduct.tprod ℂ (Function.update b i (b₀ i))
      have hTensor :
          (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i v)) =
            (evalLocal i v) • (a ⊗ₜ[ℂ] y) :=
        (congrArg (fun f => a ⊗ₜ[ℂ] f) hProd).trans
          (TensorProduct.tmul_smul (R := ℂ) (evalLocal i v) a y)
      exact (congrArg embed hTensor).trans (embed.map_smul (evalLocal i v) (a ⊗ₜ[ℂ] y))
    let q := placeTuplePoint 1 (Function.update g i 1)
    let c := evalLocal i v
    change cuspWhittaker F T χ _ (placeTuplePoint 1 (Function.update g i h)) =
      cuspWhittaker F T χ x q * (c * C i h)
    calc
      _ = cuspWhittaker F T χ (c • x) (q₀ i h * q) :=
        congrArg₂ (cuspWhittaker F T χ) hx (placeTuplePoint_update_rankOne i g h)
      _ = cuspFunction F T (c • x) (q₀ i h * q) :=
        congrFun (RealRankZero.cuspWhittaker_rankZero T χ (c • x)) _
      _ = c * cuspFunction F T x (q₀ i h * q) :=
        RealPlaceWhittaker.cuspFunction_smul_apply F T c x _
      _ = c * (C i h * cuspFunction F T x q) :=
        congrArg (c * ·) (cuspFunction_mul_rankOne T hω hx₀ x (q₀ i h) q)
      _ = c * (C i h * cuspWhittaker F T χ x q) :=
        congrArg (fun z => c * (C i h * z)) (congrFun (RealRankZero.cuspWhittaker_rankZero T χ x) q).symm
      _ = _ := by ac_rfl

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
