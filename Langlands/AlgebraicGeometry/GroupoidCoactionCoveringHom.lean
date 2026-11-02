import Langlands.AlgebraicGeometry.GroupoidCoactionCartesianLift
import Langlands.AlgebraicGeometry.GroupoidCoactionHom

/-! # Covering coactions on Hom modules -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

section SourceAction

variable {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
variable {Y H : Type v} [AddCommGroup Y] [Module D Y] [Module B Y]
  [IsScalarTower B D Y] [AddCommGroup H] [Module B H]

/-- The covering ring acts on Hom by multiplication in its source. -/
@[instance_reducible]
def homSourceModule : Module D (Y →ₗ[B] H) where
  smul d f :=
    { toFun := fun y => f (d • y)
      map_add' := fun x y => by rw [smul_add, map_add]
      map_smul' := fun b y => by simpa only [RingHom.id_apply] using (congrArg f (smul_comm d b y)).trans (f.map_smul b (d • y)) }
  one_smul f := by
    ext y
    change f ((1 : D) • y) = f y
    rw [one_smul]
  mul_smul d d' f := by
    ext y
    change f ((d * d') • y) = f (d' • d • y)
    rw [← mul_smul, mul_comm]
  smul_zero d := by ext y; rfl
  smul_add d f g := by ext y; rfl
  add_smul d d' f := by
    ext y
    change f ((d + d') • y) = f (d • y) + f (d' • y)
    rw [add_smul, map_add]
  zero_smul f := by
    ext y
    change f ((0 : D) • y) = 0
    rw [zero_smul, map_zero]

attribute [local instance 50] homSourceModule

@[simp]
lemma homSourceModule_smul_apply (d : D) (f : Y →ₗ[B] H) (y : Y) :
    (d • f) y = f (d • y) := rfl

/-- The source action restricts to the existing scalar action on Hom. -/
theorem homSourceTower : IsScalarTower B D (Y →ₗ[B] H) :=
  IsScalarTower.of_algebraMap_smul fun b f => by
    ext y
    change f (algebraMap B D b • y) = b • f y
    rw [IsScalarTower.algebraMap_smul, f.map_smul]

end SourceAction

attribute [local instance 50] homSourceModule homSourceTower

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]
  [Algebra B P] [IsScalarTower B D P]
variable (e : P ≃ₐ[D] D ⊗[B] C)
variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
variable {Y H : Type v} [AddCommGroup Y] [Module D Y] [Module B Y]
  [IsScalarTower B D Y] [AddCommGroup H] [Module B H]

section TensorEvaluation

variable [Module.Flat B C] [Module.FinitePresentation B Y]

omit [Module.Flat B C] in
lemma pushforwardTensorEquiv_mul_base_tmul
    {X : Type v} [AddCommGroup X] [Module D X] [Module B X] [IsScalarTower B D X]
    (d : D) (a c : C) (x : X) :
    pushforwardTensorEquiv e
        (e.symm (d ⊗ₜ[B] a) • (cartesianBaseMap e c ⊗ₜ[D] x)) =
      (a * c) ⊗ₜ[B] (d • x) := by
  rw [smul_tmul', smul_eq_mul, cartesianBaseMap_apply, ← map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, pushforwardTensorEquiv_tmul]

/-- Evaluation balances the covering relation-ring action between Hom and its source. -/
lemma homTensorEquiv_cartesian_balance
    (p : P) (x : P ⊗[D] (Y →ₗ[B] H)) (y : P ⊗[D] Y) :
    homTensorEquiv (B := B) (S := C) (G := Y) (M := H)
        (pushforwardTensorEquiv e (p • x)) (pushforwardTensorEquiv e y) =
      homTensorEquiv (B := B) (S := C) (G := Y) (M := H)
        (pushforwardTensorEquiv e x) (pushforwardTensorEquiv e (p • y)) := by
  obtain ⟨x, rfl⟩ := (pushforwardTensorEquiv (M := Y →ₗ[B] H) e).symm.surjective x
  obtain ⟨y, rfl⟩ := (pushforwardTensorEquiv (M := Y) e).symm.surjective y
  induction x using TensorProduct.inductionOn with
  | tmul c f =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      obtain ⟨q, rfl⟩ := e.symm.surjective p
      induction q using TensorProduct.inductionOn with
      | tmul d a =>
        simp only [pushforwardTensorEquiv_symm_tmul, pushforwardTensorEquiv_mul_base_tmul,
          pushforwardTensorEquiv_base_tmul, homTensorEquiv_tmul_apply,
          homSourceModule_smul_apply]
        rw [mul_assoc, mul_left_comm c a b]
      | add p q hp hq =>
        simp only [map_add, add_smul, LinearMap.add_apply, hp, hq]
    | add y z hy hz =>
      simp only [map_add, smul_add, hy, hz]
  | add x z hx hz =>
    simp only [map_add, smul_add, LinearMap.add_apply, hx, hz]

end TensorEvaluation

variable [Module.FinitePresentation B Y]
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable (ψ : GroupoidCoaction td Y) (θ : GroupoidCoaction t H)

/-- Target semilinearity for the cartesian lift of the actual base Hom coaction. -/
lemma cartesianLiftMap_hom_smul (d : D) (f : Y →ₗ[B] H) :
    cartesianLiftMap e (hom hE (pushforward e ht ψ hE hP) θ) (d • f) =
      td d • cartesianLiftMap e (hom hE (pushforward e ht ψ hE hP) θ) f := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  apply (pushforwardTensorEquiv e).injective
  rw [pushforwardTensorEquiv_cartesianLiftMap]
  apply (homTensorEquiv (B := B) (S := C) (G := Y) (M := H)).injective
  apply linearMap_ext_coaction hE (pushforward e ht ψ hE hP) (AlgHom.id B C)
  intro y
  simp only [show (AlgHom.id B C).toLinearMap = (LinearMap.id : C →ₗ[B] C) from rfl,
    LinearMap.rTensor_id_apply]
  change homTensorEquiv (B := B) (S := C) (G := Y) (M := H)
      (homCoactionMap hE (pushforward e ht ψ hE hP) θ (d • f))
      (pushforwardTensorEquiv e (ψ.coaction y)) =
    homTensorEquiv (B := B) (S := C) (G := Y) (M := H)
      (pushforwardTensorEquiv e (td d •
        cartesianLiftMap e (hom hE (pushforward e ht ψ hE hP) θ) f))
      (pushforwardTensorEquiv e (ψ.coaction y))
  have hy := homCoactionMap_eval hE (pushforward e ht ψ hE hP) θ (d • f) y
  change homTensorEquiv (B := B) (S := C) (G := Y) (M := H)
      (homCoactionMap hE (pushforward e ht ψ hE hP) θ (d • f))
      (pushforwardTensorEquiv e (ψ.coaction y)) = θ.coaction ((d • f) y) at hy
  rw [hy, homTensorEquiv_cartesian_balance e]
  change θ.coaction ((d • f) y) =
    homTensorEquiv (B := B) (S := C) (G := Y) (M := H)
      (pushforwardTensorEquiv e
        (cartesianLiftMap e (hom hE (pushforward e ht ψ hE hP) θ) f))
      (pushforwardTensorEquiv e (td d • ψ.coaction y))
  rw [pushforwardTensorEquiv_cartesianLiftMap, ← ψ.map_smul]
  exact (homCoactionMap_eval hE (pushforward e ht ψ hE hP) θ f (d • y)).symm

/-- The covering coaction on Hom over the base ring, with its source scalar action. -/
noncomputable def coveringHom : GroupoidCoaction td (Y →ₗ[B] H) :=
  cartesianLiftCoaction e ht (hom hE (pushforward e ht ψ hE hP) θ)
    (cartesianLiftMap_hom_smul e ht hE hP ψ θ)

@[simp]
lemma pushforward_coveringHom :
    pushforward e ht (coveringHom e ht hE hP ψ θ) hE hP =
      hom hE (pushforward e ht ψ hE hP) θ :=
  pushforward_cartesianLiftCoaction e ht _ _ hE hP

end Langlands.AlgebraicGeometry.GroupoidCoaction
