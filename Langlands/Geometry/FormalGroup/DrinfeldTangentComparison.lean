import Langlands.Geometry.FormalGroup.DrinfeldTangentUniformizer

/-! # Derivatives of actual order-linear maps on Drinfeld tangent components -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple ModuleLaw

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentComparisonLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable {I J : Type} [Finite I] [Finite J] {M : ModuleLaw 𝒪[K] B.obj I} {N : ModuleLaw 𝒪[K] B.obj J}
  {E : OrderAction (IntegerRing K D) M} {E' : OrderAction (IntegerRing K D) N}

local notation "d" => CentralSimple.reducedDegree K D
local notation "W" => drinfeldTangentComponent ι hL χ ψ E
local notation "W'" => drinfeldTangentComponent ι hL χ ψ E'
local notation "iC" => subfieldIntegerInclusion K D ι
local notation "θ" => (fun i : Fin d => subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL χ i) ψ)

/-- An actual order-linear formal homomorphism induces linear maps on the tangent summands. -/
def drinfeldTangentComponentHom (f : OrderAction.Hom E E') (i : Fin d) :
    W i →ₗ[B.obj] W' i :=
  ((f.val.fiberTangent (RingHom.id B.obj)).comp (W i).subtype).codRestrict (W' i) (fun x => by
    apply (mem_drinfeldTangentComponent_iff ι χ ψ hL E' i _).mpr
    intro a
    have hx := (mem_drinfeldTangentComponent_iff ι χ ψ hL E i x.val).mp x.property a
    let f₁ := f.val.fiberTangent (RingHom.id B.obj)
    have h := LinearMap.congr_fun (OrderAction.Hom.fiberTangent_commutes f (RingHom.id B.obj) (iC a))
      x.val
    change f₁ (E.tangentAction (iC a) x.val) = E'.tangentAction (iC a) (f₁ x.val) at h
    change E'.tangentAction (iC a) (f₁ x.val) = θ i a • f₁ x.val
    rw [← h, hx, map_smul])

@[simp]
theorem drinfeldTangentComponentHom_coe (f : OrderAction.Hom E E') (i : Fin d) (x : W i) :
    (drinfeldTangentComponentHom ι hL χ ψ f i x).val =
      f.val.fiberTangent (RingHom.id B.obj) x.val := rfl

/-- An actual order-linear isomorphism induces isomorphisms of the homogeneous tangent modules. -/
def drinfeldTangentComponentIso (f : OrderAction.Iso E E') (i : Fin d) :
    W i ≃ₗ[B.obj] W' i :=
  LinearEquiv.ofLinearMap (drinfeldTangentComponentHom ι hL χ ψ f.hom i)
    (drinfeldTangentComponentHom ι hL χ ψ f.inv i)
    (LinearMap.ext fun x => Subtype.ext ((f.toModuleIso.fiberTangent (RingHom.id B.obj)).apply_symm_apply
      x.val))
    (LinearMap.ext fun x => Subtype.ext ((f.toModuleIso.fiberTangent (RingHom.id B.obj)).symm_apply_apply
      x.val))

end Langlands.FormalGroup.LocalDivision
