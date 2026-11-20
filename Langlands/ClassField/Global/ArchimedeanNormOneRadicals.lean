import Langlands.ClassField.Global.ArchimedeanTensorUnits

/-! # Archimedean radicals for norm-one torsion cocycles -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.ClassField.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Global.AdelicFunctoriality ClassFieldTheory.Local

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B : Type u} [Field F] [Field B] [NumberField F] [NumberField B] [Algebra F B]
  (v : InfinitePlace F) {M : Type u} [Field M] [Algebra v.Completion M] [Algebra F M]
  [IsScalarTower F v.Completion M]

local notation "K" => InfinitePlace.Completion v
local notation "I" => InfinitePlacesAbove B v

private def completionTensorEquiv : B ⊗[F] K ≃+* ((w : I) → w.1.Completion) :=
  (Algebra.TensorProduct.comm F B K).toRingEquiv.trans (infiniteTensorEquiv v).toRingEquiv

private theorem completionTensorEquiv_tmul (b : B) (k : K) (w : I) :
    completionTensorEquiv v (b ⊗ₜ[F] k) w =
      algebraMap K w.1.Completion k * algebraMap B w.1.Completion b := by
  change infiniteTensorEquiv v (k ⊗ₜ[F] b) w = _
  rw [infiniteTensorEquiv_apply, infiniteTensorMap_tmul]
  rfl

/-- Units of the tensor with an infinite completion are tuples of units in the
completions of the extension above that place. -/
def archimedeanCompletionUnitsEquiv : (B ⊗[F] K)ˣ ≃* ((w : I) → w.1.Completionˣ) :=
  (Units.mapEquiv (completionTensorEquiv (B := B) v).toMulEquiv).trans MulEquiv.piUnits

/-- Global units in the completed tensor have their ordinary unit images as coordinates. -/
theorem archimedeanCompletionUnitsEquiv_left (b : Bˣ) (w : I) :
    archimedeanCompletionUnitsEquiv v (leftTensorUnit b) w =
      Units.map (algebraMap B w.1.Completion).toMonoidHom b := by
  apply Units.ext
  change completionTensorEquiv v ((b : B) ⊗ₜ[F] (1 : K)) w = _
  rw [completionTensorEquiv_tmul, map_one, one_mul]
  rfl

/-- On extending the completion tensor to a larger coefficient field, each completed
coordinate becomes a unit from the left factor. -/
theorem archimedeanTensorUnitsEquiv_extend (x : (B ⊗[F] K)ˣ) (w : I) :
    archimedeanTensorUnitsEquiv v (extendTensorUnit M x) w =
      leftTensorUnit (archimedeanCompletionUnitsEquiv v x w) := by
  apply Units.ext
  change archimedeanTensorEquiv v
      (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom F K M) (x : B ⊗[F] K)) w =
    completionTensorEquiv v (x : B ⊗[F] K) w ⊗ₜ[K] (1 : M)
  generalize (x : B ⊗[F] K) = t
  induction t using TensorProduct.inductionOn with
  | tmul b k =>
    change archimedeanTensorEquiv v (b ⊗ₜ[F] algebraMap K M k) w = _
    rw [archimedeanTensorEquiv_tmul, completionTensorEquiv_tmul]
    calc
      _ = (algebraMap B w.1.Completion b) ⊗ₜ[K] (k • (1 : M)) := by
        rw [Algebra.smul_def, mul_one]
      _ = (k • algebraMap B w.1.Completion b) ⊗ₜ[K] (1 : M) :=
        (TensorProduct.smul_tmul k _ _).symm
      _ = _ := by rw [Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, TensorProduct.add_tmul, hx, hy]

/-- Units extended from the completion tensor are fixed by the local Galois action. -/
theorem tensorAction_extendCompletion (σ : Gal(M/K)) (x : (B ⊗[F] K)ˣ) :
    tensorAction F B M (σ.restrictScalars F) (extendTensorUnit M x) = extendTensorUnit M x := by
  apply (archimedeanTensorUnitsEquiv v).injective
  funext w
  rw [archimedeanTensorUnitsEquiv_action, archimedeanTensorUnitsEquiv_extend,
    tensorAction_leftTensorUnit]

variable [FiniteDimensional v.Completion M] [IsGalois v.Completion M] [IsAlgClosed M]

/-- A norm-one torsion cocycle has a tensor-unit radical over the local coefficient field.
Its power descends to the completion tensor, and its norm descends to a unit of the completion. -/
theorem exists_archimedeanNormOneRadical (n : ℕ) (c : Gal(M/K) → (B ⊗[F] M)ˣ)
    (hc : ∀ σ τ, c (σ * τ) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ)
    (hp : ∀ σ, c σ ^ n = 1) (hN : ∀ σ, tensorNormUnits F B M (c σ) = 1) :
    ∃ (x : (B ⊗[F] M)ˣ) (b : (B ⊗[F] K)ˣ) (s : Kˣ),
      x ^ n = extendTensorUnit M b ∧
      tensorNormUnits F B M x = Units.map (algebraMap K M).toMonoidHom s ∧
      tensorNormUnits F B K b = s ^ n ∧
      ∀ σ, tensorAction F B M (σ.restrictScalars F) x / x = c σ := by
  obtain ⟨x, hx⟩ := exists_archimedeanTensorCoboundary v c hc
  have hpow (σ : Gal(M/K)) : tensorAction F B M (σ.restrictScalars F) (x ^ n) = x ^ n := by
    apply div_eq_one.mp
    rw [map_pow, ← div_pow, hx, hp]
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let e := archimedeanTensorUnitsEquiv (B := B) (M := M) v
  have hcoord (w : I) : ∃ y : w.1.Completionˣ, leftTensorUnit y = e (x ^ n) w := by
    apply exists_leftTensorUnit_of_fixed
    intro σ
    rw [← archimedeanTensorUnitsEquiv_action, hpow]
  choose y hy using hcoord
  let q := archimedeanCompletionUnitsEquiv (B := B) v
  let b := q.symm y
  have hb : x ^ n = extendTensorUnit M b := by
    apply e.injective
    funext w
    change e (x ^ n) w = archimedeanTensorUnitsEquiv v (extendTensorUnit M b) w
    rw [archimedeanTensorUnitsEquiv_extend, show q b = y from q.apply_symm_apply y, hy]
  let N := tensorNormUnits F B M
  have hfix (σ : Gal(M/K)) : σ • N x = N x := by
    apply div_eq_one.mp
    rw [show σ • N x = N (tensorAction F B M (σ.restrictScalars F) x) from
      (tensorNormUnits_action (σ.restrictScalars F) x).symm, ← map_div, hx]
    exact hN σ
  let t : (unitsRepresentation K M).ρ.invariants := ⟨Additive.ofMul (N x), hfix⟩
  obtain ⟨s, hs⟩ := baseUnitsToInvariants_surjective K M t
  have hs' : Units.map (algebraMap K M).toMonoidHom s.toMul = N x :=
    congrArg (fun z : (unitsRepresentation K M).ρ.invariants => Additive.toMul z.val) hs
  refine ⟨x, b, s.toMul, hb, hs'.symm, ?_, hx⟩
  apply Units.map_injective (f := (algebraMap K M).toMonoidHom) (algebraMap K M).injective
  calc
    Units.map (algebraMap K M).toMonoidHom (tensorNormUnits F B K b) =
        N (extendTensorUnit M b) := (tensorNormUnits_extend M b).symm
    _ = N (x ^ n) := congrArg N hb.symm
    _ = (N x) ^ n := map_pow N x n
    _ = Units.map (algebraMap K M).toMonoidHom s.toMul ^ n := congrArg (· ^ n) hs'.symm
    _ = Units.map (algebraMap K M).toMonoidHom (s.toMul ^ n) := (map_pow _ _ _).symm

end Langlands.ClassField.Global.TensorUnitShapiro
