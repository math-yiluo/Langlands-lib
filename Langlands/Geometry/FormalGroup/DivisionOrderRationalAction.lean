import Langlands.Geometry.FormalGroup.DivisionOrderScalarExtension
import Langlands.Geometry.FormalGroup.RationalEndAlgebra

/-! # Rational extension of the actual division-order action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel TensorProduct ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {S : Type w} [CommRing S] [Algebra 𝒪[K] S]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] R σ}

local instance : Algebra 𝒪[K] (RationalHom K M M) :=
  Algebra.compHom _ (algebraMap 𝒪[K] K)

local instance : IsScalarTower 𝒪[K] K (RationalHom K M M) :=
  .of_algebraMap_eq (fun _ => rfl)

private def integralAction (E : OrderAction (IntegerRing K D) M) :
    IntegerRing K D →ₐ[𝒪[K]] RationalHom K M M where
  toRingHom := RationalHom.ofHomEnd.comp E.action
  commutes' a := by
    have h : E.action (algebraMap 𝒪[K] (IntegerRing K D) a) = a • Hom.id M := by
      apply Hom.ext
      rw [E.extends_scalars, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id]
    change RationalHom.ofHom (F := K) (E.action (algebraMap 𝒪[K] (IntegerRing K D) a)) =
      (algebraMap 𝒪[K] K a) • RationalHom.id M
    rw [h]
    change (1 : K) ⊗ₜ[𝒪[K]] (a • Hom.id M) =
      (algebraMap 𝒪[K] K a) • ((1 : K) ⊗ₜ[𝒪[K]] Hom.id M)
    rw [← TensorProduct.smul_tmul, ← IsScalarTower.algebraMap_smul K a (1 : K),
      TensorProduct.smul_tmul']

/-- Extend the original order action to rational formal endomorphisms over the division algebra. -/
def rationalAction (E : OrderAction (IntegerRing K D) M) : D →ₐ[K] RationalHom K M M :=
  (AlgHom.liftEquiv 𝒪[K] K (IntegerRing K D) (RationalHom K M M)
    (integralAction K D E)).comp (integerTensorEquiv K D).symm.toAlgHom

/-- On the original order, the action is the rationalization of the actual integral endomorphism. -/
@[simp]
theorem rationalAction_coe (E : OrderAction (IntegerRing K D) M) (a : IntegerRing K D) :
    rationalAction K D E (a : D) = RationalHom.ofHom (E.action a) := by
  simp only [rationalAction, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, integerTensorEquiv_symm_coe,
    AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- Agreement on the actual integer order detects equality of algebra maps out of `D`. -/
theorem algHom_ext_onIntegers {B : Type*} [Semiring B] [Algebra K B] {f g : D →ₐ[K] B}
    (h : ∀ a : IntegerRing K D, f (a : D) = g (a : D)) : f = g := by
  apply AlgHom.ext
  intro d
  obtain ⟨t, rfl⟩ := (integerTensorEquiv K D).surjective d
  induction t using TensorProduct.inductionOn with
  | tmul k a => rw [integerTensorEquiv_tmul, map_smul, map_smul, h a]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Extending the formal coefficients commutes with the actual rational division-algebra action. -/
theorem rationalAction_map (E : OrderAction (IntegerRing K D) M) (θ : R →ₐ[𝒪[K]] S) :
    (RationalHom.mapEnd θ).comp (rationalAction K D E) = rationalAction K D (E.map θ) := by
  apply algHom_ext_onIntegers K D
  intro a
  change RationalHom.map θ (rationalAction K D E (a : D)) =
    rationalAction K D (E.map θ) (a : D)
  rw [rationalAction_coe, rationalAction_coe, RationalHom.map_ofHom, OrderAction.map_action]

@[simp]
theorem rationalAction_map_apply (E : OrderAction (IntegerRing K D) M)
    (θ : R →ₐ[𝒪[K]] S) (d : D) :
    RationalHom.map θ (rationalAction K D E d) = rationalAction K D (E.map θ) d :=
  DFunLike.congr_fun (rationalAction_map K D E θ) d

end Langlands.FormalGroup.LocalDivision
