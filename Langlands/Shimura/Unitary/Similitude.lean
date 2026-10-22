import Langlands.Shimura.Unitary.Involution
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-! # Unitary similitude groups as functors on commutative algebras -/

universe u v w z

namespace Langlands.Shimura.AlgebraInvolution

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Embed invertible scalars in the algebra's group of units. -/
def scalarUnits : Rˣ →* Aˣ := Units.map (algebraMap R A).toMonoidHom

theorem scalarUnits_commute (c : Rˣ) (a : Aˣ) :
    Commute (scalarUnits (A := A) c) a :=
  Units.ext (Algebra.commutes (c : R) (a : A))

variable (σ : AlgebraInvolution R A)

/-- A multiplicative map used to express the similitude equation as an equalizer. -/
def similitudeCompanion : Aˣ × Rˣ →* Aˣ where
  toFun x := scalarUnits x.2 * σ.inverseUnits x.1
  map_one' := by simp
  map_mul' x y := by
    change scalarUnits (x.2 * y.2) * σ.inverseUnits (x.1 * y.1) =
      (scalarUnits x.2 * σ.inverseUnits x.1) *
        (scalarUnits y.2 * σ.inverseUnits y.1)
    rw [_root_.map_mul, _root_.map_mul]
    exact (scalarUnits_commute y.2 (σ.inverseUnits x.1)).mul_mul_mul_comm _ _

/-- Pairs `(g,c)` with `g σ(g) = c`, with their genuine subgroup structure. -/
def similitudes : Subgroup (Aˣ × Rˣ) :=
  (MonoidHom.fst Aˣ Rˣ).eqLocus σ.similitudeCompanion

theorem mem_similitudes_iff_units (x : Aˣ × Rˣ) :
    x ∈ σ.similitudes ↔ x.1 * σ.units x.1 = scalarUnits x.2 := by
  change (x.1 = scalarUnits x.2 * σ.units x.1⁻¹) ↔ _
  rw [σ.units_inv, eq_mul_inv_iff_mul_eq]

theorem mem_similitudes_iff (x : Aˣ × Rˣ) :
    x ∈ σ.similitudes ↔ (x.1 : A) * σ x.1 = algebraMap R A x.2 := by
  rw [σ.mem_similitudes_iff_units, Units.ext_iff]
  rfl

/-- The multiplier is projection onto the scalar coordinate. -/
def multiplier : σ.similitudes →* Rˣ :=
  (MonoidHom.snd Aˣ Rˣ).comp σ.similitudes.subtype

/-- Forget the recorded multiplier. -/
def underlyingUnit : σ.similitudes →* Aˣ :=
  (MonoidHom.fst Aˣ Rˣ).comp σ.similitudes.subtype

/-- The actual unitary subgroup, as the equalizer of identity and inverse-involution. -/
def unitary : Subgroup Aˣ :=
  (MonoidHom.id Aˣ).eqLocus σ.inverseUnits.toMonoidHom

theorem mem_unitary_iff (a : Aˣ) :
    a ∈ σ.unitary ↔ (a : A) * σ a = 1 := by
  change (a = σ.units a⁻¹) ↔ _
  rw [σ.units_inv, eq_inv_iff_mul_eq_one, Units.ext_iff]
  rfl

/-- Include the unitary group with multiplier one. -/
def unitaryInclusion : σ.unitary →* σ.similitudes where
  toFun a := ⟨(a, 1), by
    rw [σ.mem_similitudes_iff]
    simpa using (σ.mem_unitary_iff a).mp a.property⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (Prod.ext rfl (one_mul 1).symm)

/-- Unitary elements identify with the kernel of the multiplier. -/
def unitaryEquivKernel : σ.unitary ≃* σ.multiplier.ker where
  toFun a := ⟨σ.unitaryInclusion a, by rfl⟩
  invFun x := ⟨x.1.1.1, by
    rw [σ.mem_unitary_iff]
    have hx := (σ.mem_similitudes_iff x.1.1).mp x.1.property
    have hc : x.1.1.2 = 1 := x.property
    simpa [hc] using hx⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  map_mul' a b := Subtype.ext (_root_.map_mul σ.unitaryInclusion a b)

/-- The multiplier is unique whenever the scalar embedding is injective. -/
theorem underlyingUnit_injective
    (hR : Function.Injective (algebraMap R A)) :
    Function.Injective σ.underlyingUnit := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext h
  apply Units.ext
  apply hR
  change algebraMap R A (x.1.2 : R) = algebraMap R A (y.1.2 : R)
  rw [← (σ.mem_similitudes_iff x.1).mp x.property,
      ← (σ.mem_similitudes_iff y.1).mp y.property]
  change x.1.1 = y.1.1 at h
  rw [h]

section Maps

variable {S : Type w} {B : Type z}
variable [CommRing S] [Ring B] [Algebra S B]
variable (τ : AlgebraInvolution S B)

/-- The map on similitude groups induced by compatible actual algebra maps. -/
def map (f : A →+* B) (g : R →+* S)
    (hf : ∀ a, f (σ a) = τ (f a))
    (hg : ∀ r, f (algebraMap R A r) = algebraMap S B (g r)) :
    σ.similitudes →* τ.similitudes where
  toFun x := ⟨(Units.map f.toMonoidHom x.1.1, Units.map g.toMonoidHom x.1.2), by
    rw [τ.mem_similitudes_iff]
    change f (x.1.1 : A) * τ (f (x.1.1 : A)) = algebraMap S B (g (x.1.2 : R))
    rw [← hf, ← f.map_mul, (σ.mem_similitudes_iff x.1).mp x.property, hg]⟩
  map_one' := Subtype.ext (Prod.ext (_root_.map_one _) (_root_.map_one _))
  map_mul' x y := Subtype.ext (Prod.ext (_root_.map_mul _ _ _) (_root_.map_mul _ _ _))

theorem multiplier_map (f : A →+* B) (g : R →+* S)
    (hf : ∀ a, f (σ a) = τ (f a))
    (hg : ∀ r, f (algebraMap R A r) = algebraMap S B (g r)) (x : σ.similitudes) :
    τ.multiplier (σ.map τ f g hf hg x) = Units.map g.toMonoidHom (σ.multiplier x) :=
  rfl

end Maps

section Functor

open CategoryTheory
open scoped TensorProduct

variable {S T : CommAlgCat.{w} R}

/-- Change the coefficient algebra in the similitude group. -/
noncomputable def baseChangeMap (f : S ⟶ T) :
    (σ.baseChange S).similitudes →* (σ.baseChange T).similitudes :=
  (σ.baseChange S).map (σ.baseChange T)
    (changeCoefficients (A := A) f.hom).toRingHom f.hom.toRingHom
    (σ.changeCoefficients_involution f.hom)
    (changeCoefficients_scalar f.hom)

/-- The unitary-similitude group functor, defined on every commutative base algebra. -/
noncomputable def similitudeFunctor : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj S := GrpCat.of (σ.baseChange S).similitudes
  map f := GrpCat.ofHom (σ.baseChangeMap f)
  map_id S := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      change changeCoefficients (AlgHom.id R S) (x.1.1 : S ⊗[R] A) = x.1.1
      rw [changeCoefficients_id]
      rfl
    · apply Units.ext
      rfl
  map_comp {S T U} f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      change changeCoefficients (g.hom.comp f.hom) (x.1.1 : S ⊗[R] A) =
        changeCoefficients g.hom (changeCoefficients f.hom (x.1.1 : S ⊗[R] A))
      rw [changeCoefficients_comp]
      rfl
    · apply Units.ext
      rfl

end Functor

end Langlands.Shimura.AlgebraInvolution
