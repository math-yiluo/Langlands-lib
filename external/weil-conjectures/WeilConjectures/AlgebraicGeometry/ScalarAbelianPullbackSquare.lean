/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ScalarForgetPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ScalarStructureCoefficientAdjunct

/-! # The underlying abelian square for scalar inverse image

Source: Stacks Project, Tag 01F7; Modules, Tag 0096.
(blueprint: new-sc-scalar-abelian-pullback-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] scalarAbelianUnitClass scalarInverseImage
attribute [local instance] instHasExtKSheaf

/-- Abelian inverse image along a scheme morphism, as in structure-sheaf pullback.
Source: Stacks Project, Tag 01F7.
(blueprint: new-sc-scalar-abelian-pullback-square). -/
noncomputable abbrev scalarAbelianInverseImage {X Y : Scheme.{u}} (a : Y ⟶ X) :=
  (Opens.map a.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

instance {X Y : Scheme.{u}} (a : Y ⟶ X) :
    PreservesFiniteLimits (scalarAbelianInverseImage a) := by
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map a.base)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

noncomputable instance {X Y : Scheme.{u}} (a : Y ⟶ X) :
    PreservesFiniteColimits (scalarAbelianInverseImage a) := by
  have := ((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjoint_preservesColimits
  infer_instance

instance {X Y : Scheme.{u}} (a : Y ⟶ X) :
    (scalarAbelianInverseImage a).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (scalarAbelianInverseImage a)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The abelian coefficient map adjoint to the structure-sheaf morphism.
Source: Stacks Project, Tag 01F7.
(blueprint: new-sc-scalar-abelian-pullback-square). -/
noncomputable abbrev scalarAbelianStructureCoefficient {X Y : Scheme.{u}} (a : Y ⟶ X) :=
  (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
    (structureSheafAb X) (structureSheafAb Y)).symm
      (⟨Functor.whiskerRight a.c
        (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)

/-- The comparison from the target integer sheaf to inverse image of the source integer sheaf.
Source: Stacks Project, Tag 01F7; constant-sheaf adjunction.
(blueprint: new-sc-scalar-abelian-pullback-square). -/
noncomputable abbrev scalarAbelianIntegerIso {X Y : Scheme.{u}} (a : Y ⟶ X) :=
  ((Opens.map a.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))

/-- The defining Ext formula for structure-sheaf pullback.
Source: Stacks Project, Tag 01F7.
(blueprint: new-sc-scalar-abelian-pullback-square). -/
theorem scalarAbelianStructurePullback_apply {X Y : Scheme.{u}} (a : Y ⟶ X)
    (n : ℕ) (x : Sheaf.H (structureSheafAb X) n) :
    structureSheafCohomologyPullback a n x =
      ((Abelian.Ext.mk₀ (scalarAbelianIntegerIso a).hom).comp
        (x.mapExactFunctor (scalarAbelianInverseImage a)) (zero_add n)).comp
        (Abelian.Ext.mk₀ (scalarAbelianStructureCoefficient a)) (add_zero n) := by
  rfl

/-- The canonical square of inverse image and forgetting scalars carries both the
integer-unit generator and the tensor-unit coefficient to their abelian counterparts.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial;
Modules, Tag 0096, inverse-image/direct-image adjunction.
(blueprint: new-sc-scalar-abelian-pullback-square).

Proof: Form the canonical comparison from abelian inverse image of the underlying
scalar sheaf to the underlying sheaf of scalar inverse image. Its adjunct is the
forgotten scalar adjunction unit; it is an isomorphism because both inverse images
have the same stalks and forgetting scalars commutes with filtered colimits.
Invert this comparison to obtain c, naturally in the coefficient sheaf. The
constant-sheaf adjunction identifies its unit component: the integer generator
maps to the scalar section 1, scalarInverseUnitIso transports the scalar section
1 to the same section on Y, and scalarAbelianIntegerIso transports the integer
generator to that section. Equality under the sections adjunction gives the first
(degree-zero) equation. For the second equation apply the abelian inverse-image
adjunction. The characterization in exists_scalarPullbackCoefficient identifies
its sectionwise adjunct with the tensor adjunction unit. Postcomposition with
tensorPullbackObjUnitToUnit gives the original structure-sheaf morphism, by
tensorPullbackObjUnitToUnit_isIso. This is the adjunct defining
scalarAbelianStructureCoefficient. Injectivity of the adjunction equivalence gives
the equation. These are sheaf-map and degree-zero identities, with no higher
cohomology class, module Ext comparison, or resolution choices. On the empty
scheme all involved sections and identities are zero; no nonemptiness is needed. -/
theorem scalar_abelian_pullback_square (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g) :
    ∃ c : scalarInverseImage (k := k) a ⋙ scalarAbelianForget k Y ≅
        scalarAbelianForget k X ⋙ scalarAbelianInverseImage a,
      ((scalarAbelianUnitClass k Y).comp
        (Abelian.Ext.mk₀ ((scalarAbelianForget k Y).map (scalarInverseUnitIso a).inv))
        rfl).comp
          (Abelian.Ext.mk₀ (c.hom.app (𝟙_ (KSheaf X k)))) rfl =
        (Abelian.Ext.mk₀ (scalarAbelianIntegerIso a).hom).comp
          ((scalarAbelianUnitClass k X).mapExactFunctor (scalarAbelianInverseImage a))
          rfl ∧
      (scalarAbelianForget k Y).map
          (scalarPullbackCoefficient f g a h (SheafOfModules.unit X.ringCatSheaf) ≫
            scalarHom g (tensorPullbackObjUnitToUnit a)) =
        c.hom.app (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)) ≫
          scalarAbelianStructureCoefficient a := by
  obtain ⟨c, hadj, hunit⟩ := scalar_forget_pullback_adjunction k a
  refine ⟨c, ?_, ?_⟩
  · rw [← Abelian.Ext.mk₀_homEquiv₀_apply (scalarAbelianUnitClass k Y),
      ← Abelian.Ext.mk₀_homEquiv₀_apply (scalarAbelianUnitClass k X),
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg Abelian.Ext.mk₀ (by simpa only [Category.assoc] using hunit)
  · apply (Iso.inv_comp_eq (c.app _)).mp
    apply (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
      _ _).injective
    exact (hadj _ _ _).trans ((scalar_structure_coefficient_adjunct k f g a h).trans
      ((((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
        _ _).apply_symm_apply _).symm)


end AlgebraicGeometry.Scheme
