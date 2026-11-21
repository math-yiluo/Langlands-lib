import Langlands.Automorphic.OperatorTensorDescent
import Langlands.Representation.Archimedean.GKModuleDensity
import Mathlib.Algebra.Module.ULift

/-! # Operator actions on a finite-adelic and archimedean tensor -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

namespace Langlands.Global.AdelicOperatorTensor

open NumberField Langlands.Archimedean Langlands.Automorphic ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing
open scoped Classical

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "CL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

/-- One slot for the finite adelic representation and one for each infinite place. -/
abbrev Slot := Unit ⊕ (RP ⊕ CP)

/-- The archimedean carriers are lifted to the universe of the finite carrier. -/
def SlotSpace (Vf : Type u) (Vr : RP → Type) (Vc : CP → Type) (i : Slot F) : Type u :=
  match i with
  | .inl _ => Vf
  | .inr (.inl v) => ULift.{u} (Vr v)
  | .inr (.inr v) => ULift.{u} (Vc v)

instance slotSpaceAddCommGroup (Vf : Type u) (Vr : RP → Type) (Vc : CP → Type)
    [AddCommGroup Vf] [∀ v, AddCommGroup (Vr v)] [∀ v, AddCommGroup (Vc v)]
    (i : Slot F) : AddCommGroup (SlotSpace F Vf Vr Vc i) :=
  match i with
  | .inl _ => inferInstanceAs (AddCommGroup Vf)
  | .inr (.inl v) => inferInstanceAs (AddCommGroup (ULift (Vr v)))
  | .inr (.inr v) => inferInstanceAs (AddCommGroup (ULift (Vc v)))

instance slotSpaceModule (Vf : Type u) (Vr : RP → Type) (Vc : CP → Type)
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (i : Slot F) : Module ℂ (SlotSpace F Vf Vr Vc i) :=
  match i with
  | .inl _ => inferInstanceAs (Module ℂ Vf)
  | .inr (.inl v) => inferInstanceAs (Module ℂ (ULift (Vr v)))
  | .inr (.inr v) => inferInstanceAs (Module ℂ (ULift (Vc v)))

/-- The algebraic tensor with the grouped finite slot. -/
abbrev Space (Vf : Type u) (Vr : RP → Type) (Vc : CP → Type)
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)] :=
  PiTensorProduct ℂ (SlotSpace F Vf Vr Vc)

/-- The finite translations and the compact and complexified Lie generators. -/
def Generator : Slot F → Type u
  | .inl _ => FiniteAdelicGL F n
  | .inr (.inl _) => ULift.{u} (RK ⊕ RL)
  | .inr (.inr _) => ULift.{u} (CK ⊕ CL)

/-- Map a local operator to its index among the common free generators. -/
def operatorIndex : (i : Slot F) → Generator F n i → OperatorIndex F n
  | .inl _, d => .inl (.inl d)
  | .inr (.inl v), ⟨.inl k⟩ => .inl (.inr (realPlaceCompactInclusion F n v k))
  | .inr (.inl v), ⟨.inr X⟩ => .inr (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X))
  | .inr (.inr v), ⟨.inl k⟩ => .inl (.inr (complexPlaceCompactInclusion F n v k))
  | .inr (.inr v), ⟨.inr X⟩ => .inr (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X))

/-- A local operator lifted into the common free algebra. -/
abbrev liftGenerator (i : Slot F) (g : Generator F n i) : FreeOperatorAlgebra F n :=
  FreeAlgebra.ι ℂ (operatorIndex F n i g)

/-- Act by the operator on its individual carrier, with transport along the
canonical linear equivalences for the lifted archimedean carriers. -/
def generatorAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v))
    (i : Slot F) : Generator F n i → Module.End ℂ (SlotSpace F Vf Vr Vc i) :=
  match i with
  | .inl _ => fin
  | .inr (.inl v) => fun g =>
      ULift.moduleEquiv.symm.conjAlgEquiv ℂ (GKModuleDensity.gens (κr v) (δr v) g.down)
  | .inr (.inr v) => fun g =>
      ULift.moduleEquiv.symm.conjAlgEquiv ℂ (GKModuleDensity.gens (κc v) (δc v) g.down)

/-- Compatibility of a global free action with the specified place actions. -/
abbrev HasActions {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v))
    (ρ : Representation ℂ (FreeOperatorAlgebra F n) (Space F Vf Vr Vc)) : Prop :=
  HasTensorSlotActions ρ (generatorAction F n fin κr δr κc δc) (liftGenerator F n)

end Langlands.Global.AdelicOperatorTensor
