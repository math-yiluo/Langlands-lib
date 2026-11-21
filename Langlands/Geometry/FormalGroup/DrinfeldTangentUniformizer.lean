import Langlands.Geometry.FormalGroup.DrinfeldTangentComponents

/-! # The degree-one operator on the actual Drinfeld tangent components -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple ModuleLaw

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentUniformizerLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)

local notation "C" => SubfieldIntegerRing K D ι
local notation "d" => CentralSimple.reducedDegree K D
local notation "iC" => subfieldIntegerInclusion K D ι

local instance tangentUniformizerDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

section Eigenspace

variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable {I : Type} [Finite I] {M : ModuleLaw 𝒪[K] B.obj I}
  (E : OrderAction (IntegerRing K D) M)

local notation "θ" => (fun i : Fin d => subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL χ i) ψ)
local notation "A" => drinfeldTangentCharacterAction ι hL χ ψ E
local notation "P" => drinfeldTangentProjector ι hL χ ψ E
local notation "V" => (I → B.obj)
local notation "W" => drinfeldTangentComponent ι hL χ ψ E

private theorem drinfeldTangentProjector_character_right (a : C) (i : Fin d) :
    P i * E.tangentAction (iC a) = θ i a • P i := by
  have hc : Commute (P i) (E.tangentAction (iC a)) := by
    rw [← drinfeldTangentCharacterAction_coeff ι hL χ ψ E a]
    exact (show Commute (Pi.single i (1 : B.obj)) (fun j => θ j a) from mul_comm _ _).map A
  exact hc.eq.trans (drinfeldTangentProjector_character ι hL χ ψ E a i)

/-- The image of the tangent projector is exactly its common coefficient eigenspace. -/
theorem mem_drinfeldTangentComponent_iff (i : Fin d) (x : V) :
    x ∈ W i ↔ ∀ a : C, E.tangentAction (iC a) x = θ i a • x := by
  constructor
  · rintro ⟨y, rfl⟩ a
    exact congrArg (fun w : Module.End B.obj V => w y)
      (drinfeldTangentProjector_character ι hL χ ψ E a i)
  · intro hx
    have hz (j : Fin d) (hji : j ≠ i) : P j x = 0 := by
      obtain ⟨a, ha⟩ := subfieldCyclicCharacter_lifts_separated hL χ ψ hji
      have he := congrArg (fun w : Module.End B.obj V => w x)
        (drinfeldTangentProjector_character_right ι χ ψ hL E a j)
      change P j (E.tangentAction (iC a) x) = θ j a • P j x at he
      rw [hx, map_smul] at he
      change IsUnit (θ j a - θ i a) at ha
      apply ha.smul_left_cancel.mp
      rw [smul_zero, sub_smul, ← he, sub_self]
    have he := congrArg (fun w : Module.End B.obj V => w x)
      (sum_drinfeldTangentProjector ι hL χ ψ E)
    rw [LinearMap.sum_apply, Finset.sum_eq_single i] at he
    · exact ⟨x, he⟩
    · intro j _ hj
      exact hz j hj
    · simp

end Eigenspace

section Shift

variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable (σ : L ≃ₐ[K] L)
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "θ" => (fun i : Fin d => subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL χ i) ψ)
local notation "τ" => subfieldIntegerFrobenius ι σ hL

include hσ in
/-- On the actual test ring the next character is precomposition by inverse integral Frobenius. -/
theorem drinfeldCoefficientCharacter_succ (i : Fin d) :
    θ (i + 1) = (θ i).comp (τ).symm.toAlgHom := by
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  apply Algebra.FormallyUnramified.lift_unique (Nilp.reductionIdeal π B.obj)
    (Nilp.reductionIdeal_isNilpotent B)
  apply AlgHom.ext
  intro a
  have he (k : Fin d) (b : C) : Nilp.reductionQuotient π B.obj (θ k b) =
      ψ (subfieldCyclicCharacter ι hL χ k b) :=
    AlgHom.congr_fun (reductionQuotient_comp_subfieldCoefficientLift hL
      (subfieldCyclicCharacter ι hL χ k) ψ) b
  change Nilp.reductionQuotient π B.obj (θ (i + 1) a) =
    Nilp.reductionQuotient π B.obj (θ i ((τ).symm a))
  rw [he, he, subfieldCyclicCharacter_succ ι σ hL hσ χ i a]

end Shift

section Special

variable (Y : SpecialModule K D ι B.obj) (σ : L ≃ₐ[K] L)
variable (uniformizer : Dˣ)
  (hPow : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "W" => drinfeldTangentComponent ι Y.unramified χ ψ Y.order
local notation "Θ" => (fun i : Fin d =>
  subfieldCoefficientLift Y.unramified (subfieldCyclicCharacter ι Y.unramified χ i) ψ)
local notation "t" => Y.order.tangentAction (drinfeldIntegralUniformizer uniformizer hPow)

include hComm hσ in
/-- The derivative of the actual division uniformizer maps each tangent component to its successor. -/
def drinfeldTangentUniformizerStep (i : Fin d) : W i →ₗ[B.obj] W (i + 1) where
  toFun x := ⟨t x.val, by
    apply (mem_drinfeldTangentComponent_iff ι χ ψ Y.unramified Y.order (i + 1) _).mpr
    intro a
    have hx := (mem_drinfeldTangentComponent_iff ι χ ψ Y.unramified Y.order i x.val).mp x.property
    rw [drinfeldCoefficientCharacter_succ ι χ ψ Y.unramified σ hσ i]
    exact Y.fiberTangent_uniformizer_shift ι uniformizer σ (RingHom.id B.obj)
      (Θ i).toRingHom hPow hComm x.val hx a⟩
  map_add' x y := Subtype.ext ((t).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((t).map_smul a x.val)

/-- The reduced-degree power of the derivative is the original scalar uniformizer. -/
theorem drinfeldTangentUniformizer_pow : t ^ d =
    algebraMap B.obj (Module.End B.obj (Fin d → B.obj)) (algebraMap 𝒪[K] B.obj π) := by
  rw [← map_pow, drinfeldIntegralUniformizer_pow, AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply 𝒪[K] B.obj _ π

end Special

end Langlands.FormalGroup.LocalDivision
