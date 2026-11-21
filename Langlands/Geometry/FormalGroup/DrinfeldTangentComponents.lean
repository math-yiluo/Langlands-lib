import Langlands.Geometry.FormalGroup.DrinfeldCoefficientSplitting
import Langlands.Geometry.FormalGroup.TangentCharacters

/-! # Actual tangent character components over a Drinfeld test ring -/

noncomputable section

namespace Langlands.FormalGroup

universe u v w s

namespace ModuleLaw.OrderAction

variable {O : Type u} [CommRing O] {A : Type w} [Ring A] [Algebra O A]
  {R : Type v} [CommRing R] [Algebra O R] {I : Type} [Finite I]
  {M : ModuleLaw O R I} (E : OrderAction A M)

/-- The derivative of the order action over the coefficient ring, with its given central scalar action. -/
def tangentAction : A →ₐ[O] Module.End R (I → R) :=
  { E.fiberTangent (RingHom.id R) with
    commutes' := fun a => LinearMap.ext fun x => by
      change E.fiberTangent (RingHom.id R) (algebraMap O A a) x = a • x
      rw [E.fiberTangent_scalar, RingHom.id_apply, algebraMap_smul] }

end ModuleLaw.OrderAction

namespace LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple ModuleLaw
open scoped TensorProduct

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentComponentsLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable {I : Type} [Finite I] {M : ModuleLaw 𝒪[K] B.obj I}
  (E : OrderAction (IntegerRing K D) M)

local notation "C" => SubfieldIntegerRing K D ι
local notation "d" => CentralSimple.reducedDegree K D
local notation "T" => (I → B.obj)
local notation "θ" => (fun i : Fin d => subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL χ i) ψ)
local notation "split" => subfieldCyclicSplitting hL χ ψ
local notation "iC" => subfieldIntegerInclusion K D ι

/-- The actual split coefficient algebra acts on the tangent module. -/
def drinfeldTangentCharacterAction : (Fin d → B.obj) →ₐ[B.obj] Module.End B.obj T :=
  (((E.tangentAction).comp iC).liftEquiv 𝒪[K] B.obj C (Module.End B.obj T)).comp
    (split).symm.toAlgHom

local notation "A" => drinfeldTangentCharacterAction ι hL χ ψ E

/-- Express the action of an embedded integer through its tuple of lifted characters. -/
theorem drinfeldTangentCharacterAction_coeff (a : C) :
    A (fun i => θ i a) = E.tangentAction (iC a) := by
  have he : split (1 ⊗ₜ[𝒪[K]] a) = fun i => θ i a := by
    funext i
    rw [subfieldCyclicSplitting_tmul, one_mul]
  rw [← he]
  change (((E.tangentAction).comp iC).liftEquiv 𝒪[K] B.obj C (Module.End B.obj T))
    ((split).symm (split (1 ⊗ₜ[𝒪[K]] a))) = _
  rw [AlgEquiv.symm_apply_apply, AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- Projection to a single lifted character on the tangent module. -/
def drinfeldTangentProjector (i : Fin d) : Module.End B.obj T := A (Pi.single i 1)

local notation "P" => drinfeldTangentProjector ι hL χ ψ E

@[simp]
theorem drinfeldTangentProjector_mul_same (i : Fin d) : P i * P i = P i := by
  change A (Pi.single i 1) * A (Pi.single i 1) = A (Pi.single i 1)
  rw [← map_mul]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

theorem drinfeldTangentProjector_mul_ne {i j : Fin d} (h : i ≠ j) : P i * P j = 0 := by
  change A (Pi.single i 1) * A (Pi.single j 1) = 0
  rw [← map_mul, ← map_zero A]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k
    simp [h]
  · simp [Pi.single_apply, hk]

theorem sum_drinfeldTangentProjector : (∑ i : Fin d, P i) = 1 := by
  change (∑ i : Fin d, A (Pi.single i 1)) = 1
  rw [← map_sum, ← map_one A]
  congr 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- On each projector's image, the embedded coefficient action is its character scalar. -/
theorem drinfeldTangentProjector_character (a : C) (i : Fin d) :
    E.tangentAction (iC a) * P i = θ i a • P i := by
  rw [← drinfeldTangentCharacterAction_coeff ι hL χ ψ E a]
  change A (fun j => θ j a) * A (Pi.single i 1) = θ i a • A (Pi.single i 1)
  rw [← map_mul, Algebra.smul_def (R := B.obj), ← AlgHom.commutes A, ← map_mul]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- The actual tangent submodule for one of the lifted characters. -/
def drinfeldTangentComponent (i : Fin d) : Submodule B.obj T := LinearMap.range (P i)

local notation "W" => drinfeldTangentComponent ι hL χ ψ E

/-- The projectors give the canonical decomposition of tangent vectors into their actual character components. -/
def drinfeldTangentDecomposition : T ≃ₗ[B.obj] (∀ i : Fin d, W i) where
  toFun x i := ⟨P i x, ⟨x, rfl⟩⟩
  invFun x := ∑ i, (x i : T)
  left_inv x := by
    change (∑ i, P i x) = x
    rw [← LinearMap.sum_apply, sum_drinfeldTangentProjector ι hL χ ψ E]
    rfl
  right_inv x := by
    funext i
    apply Subtype.ext
    change P i (∑ j, (x j : T)) = (x i : T)
    rw [map_sum, Finset.sum_eq_single i]
    · obtain ⟨y, hy⟩ := (x i).property
      change P i y = (x i : T) at hy
      rw [← hy]
      exact congrArg (fun t : Module.End B.obj T => t y)
        (drinfeldTangentProjector_mul_same ι hL χ ψ E i)
    · intro j _ hj
      obtain ⟨y, hy⟩ := (x j).property
      change P j y = (x j : T) at hy
      rw [← hy]
      exact congrArg (fun t : Module.End B.obj T => t y)
        (drinfeldTangentProjector_mul_ne ι hL χ ψ E hj.symm)
    · simp
  map_add' x y := funext fun i => Subtype.ext ((P i).map_add x y)
  map_smul' a x := funext fun i => Subtype.ext ((P i).map_smul a x)

end LocalDivision
end Langlands.FormalGroup
