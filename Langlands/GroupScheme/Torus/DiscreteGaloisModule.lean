import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.DiscreteOrbitProof
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology

/-! # Finitely generated discrete absolute-Galois modules -/

noncomputable section

universe u v

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable (k : Type u) [Field k]

/-- Finite generation over the integers, inside the existing smooth category
for the Krull topology on the automorphisms of the separable closure. -/
def fgDiscreteGaloisModuleProperty :
    ObjectProperty (SmoothRep.{0, u, v} ℤ
      (SeparableClosure k ≃ₐ[k] SeparableClosure k)) :=
  fun A => @Module.Finite ℤ A _ A.obj.hV1.toAddCommMonoid A.obj.hV2

/-- Finitely generated integral modules with continuous discrete
absolute-Galois action. The module universe is independent of the field
universe, and torsion is allowed. -/
abbrev FGDiscreteGaloisModule :=
  (fgDiscreteGaloisModuleProperty.{u, v} k).FullSubcategory

namespace FGDiscreteGaloisModule

variable {k}

instance : CoeSort (FGDiscreteGaloisModule.{u, v} k) (Type v) :=
  ⟨fun A => A.obj⟩

instance (A : FGDiscreteGaloisModule.{u, v} k) : AddCommGroup A :=
  A.obj.obj.hV1

instance (A : FGDiscreteGaloisModule.{u, v} k) : Module ℤ A :=
  A.obj.obj.hV2

instance (A : FGDiscreteGaloisModule.{u, v} k) : Module.Finite ℤ A :=
  A.property

/-- The actual integral representation carried by the object. -/
abbrev representation (A : FGDiscreteGaloisModule.{u, v} k) :
    Representation ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) A :=
  A.obj.representation

theorem isSmooth (A : FGDiscreteGaloisModule.{u, v} k) :
    IsSmooth A.representation :=
  A.obj.isSmooth

/-- Bundle a finitely generated integral representation with open vector
stabilizers. No module topology is added as a global instance. -/
abbrev of {M : Type v} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (ρ : Representation ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) M)
    (hρ : IsSmooth ρ) : FGDiscreteGaloisModule.{u, v} k :=
  ⟨SmoothRep.of ρ hρ, inferInstanceAs (Module.Finite ℤ M)⟩

/-- The fully faithful inclusion into the existing smooth representation
category. -/
abbrev toSmoothRep :
    FGDiscreteGaloisModule.{u, v} k ⥤
      SmoothRep.{0, u, v} ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) :=
  (fgDiscreteGaloisModuleProperty k).ι

/-- Forget both smoothness and finite generation, retaining the actual action. -/
abbrev toRep :
    FGDiscreteGaloisModule.{u, v} k ⥤
      Rep.{v} ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) :=
  toSmoothRep ⋙ SmoothRep.toRep

instance : (toRep (k := k)).Full := inferInstance

instance : (toRep (k := k)).Faithful := inferInstance

/-- The underlying equivariant integral linear map of a morphism. -/
abbrev hom {A B : FGDiscreteGaloisModule.{u, v} k} (f : A ⟶ B) :
    A.representation.IntertwiningMap B.representation :=
  SmoothRep.hom f.hom

/-- Every equivariant integral linear map is a morphism. -/
abbrev ofHom {A B : FGDiscreteGaloisModule.{u, v} k}
    (f : A.representation.IntertwiningMap B.representation) : A ⟶ B :=
  ObjectProperty.homMk (SmoothRep.ofHom f)

@[simp] theorem hom_ofHom {A B : FGDiscreteGaloisModule.{u, v} k}
    (f : A.representation.IntertwiningMap B.representation) :
    hom (ofHom f) = f := rfl

@[simp] theorem ofHom_hom {A B : FGDiscreteGaloisModule.{u, v} k} (f : A ⟶ B) :
    ofHom (hom f) = f := rfl

@[simp] theorem hom_id (A : FGDiscreteGaloisModule.{u, v} k) :
    hom (𝟙 A) = Representation.IntertwiningMap.id A.representation := rfl

@[simp] theorem hom_comp {A B C : FGDiscreteGaloisModule.{u, v} k}
    (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = (hom g).comp (hom f) := rfl

section DiscreteTopology

variable (A : FGDiscreteGaloisModule.{u, v} k)
  [TopologicalSpace A] [DiscreteTopology A]

/-- Every orbit map is continuous for any supplied discrete topology. -/
theorem continuous_orbitMap (m : A) :
    Continuous (fun σ : SeparableClosure k ≃ₐ[k] SeparableClosure k =>
      A.representation σ m) :=
  (isSmoothVector_iff_continuous_orbitMap A.representation m).mp (A.isSmooth m)

/-- Joint continuity of the action on the discrete module. -/
theorem continuous_action :
    Continuous (fun p : (SeparableClosure k ≃ₐ[k] SeparableClosure k) × A =>
      A.representation p.1 p.2) := by
  rw [continuous_prod_of_discrete_right]
  exact A.continuous_orbitMap

/-- The actual action, bundled as a continuous map. -/
def continuousAction :
    C((SeparableClosure k ≃ₐ[k] SeparableClosure k) × A, A) where
  toFun p := A.representation p.1 p.2
  continuous_toFun := A.continuous_action

@[simp] theorem continuousAction_apply
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (m : A) :
    A.continuousAction (σ, m) = A.representation σ m := rfl

end DiscreteTopology

/-- A continuous action on a finitely generated discrete integral module gives
an object of the same category. -/
abbrev ofContinuous {M : Type v} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) M)
    (hρ : Continuous
      (fun p : (SeparableClosure k ≃ₐ[k] SeparableClosure k) × M => ρ p.1 p.2)) :
    FGDiscreteGaloisModule.{u, v} k :=
  of ρ (fun m => (isSmoothVector_iff_continuous_orbitMap ρ m).mpr
    (hρ.comp (continuous_id.prodMk continuous_const)))

end FGDiscreteGaloisModule

end Langlands.GroupScheme
