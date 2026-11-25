/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.ScalarTensorGlobalSectionsMorphism

/-! # Internal cup in degree zero on global sections

Source: Stacks Project, Cohomology, Tags 01DZ, 01F7, 0FKV.
(blueprint: lem-sc-scalar-cup-zero-global-sections).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
/-- The internal degree-zero cup evaluates to the tensor of the two global sections.
Source: Stacks Project, Cohomology, Tags 01DZ, 01F7, 0FKV.
(blueprint: lem-sc-scalar-cup-zero-global-sections).

Proof: Choose an injective resolution of each coefficient sheaf. Evaluation at 1
identifies its Hom complex from the structure sheaf with its global-section complex.
The cocycle formula specifying moduleExtEquiv, in degree zero, identifies the
rightDerivedZeroIsoSelf section with the morphism representing the Ext class.
Restriction of scalars and precomposition with scalarUnitMorphism identify that
morphism with the morphism from the constant scalar unit determined by the same
section. Thus scalarCohomologyExtEquiv in degree zero is this evaluation comparison.
Every degree-zero Ext class is mk₀ of a unique morphism. Exact-functor transport
sends mk₀ to mk₀ of the transported morphism, and composition of mk₀ classes is
mk₀ of their composite. Apply these identities to scalarExtCup: its representing
morphism is the tensor of the two representing morphisms preceded by the inverse
unit constraint. The tensorator of the sheaf-to-presheaf inclusion evaluates this
morphism to the image of the pure tensor of the two sections. The theorem
exists_scalarTensorCoefficient evaluates that image as tmulSection. Finally use the
inverse law of scalarCohomologyExtEquiv in scalarCohomologyCup. All maps are additive;
the calculation also applies to zero sections and to the empty scheme. -/
theorem scalarCohomologyCup_zero_globalSections
    (k : Type w) [Field k] (X : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules)
    (a : scalarCohomology f F 0) (b : scalarCohomology f G 0) :
    scalarGlobalSectionsEquiv f (F ⊗ G) (scalarCohomologyCup f F G 0 0 a b) =
      tmulSection (scalarGlobalSectionsEquiv f F a) (scalarGlobalSectionsEquiv f G b) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
      let : HasExt.{w + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
      let : MonoidalCategory (SheafOfModules.{w} X.ringCatSheaf) :=
        SheafOfModules.monoidalCategory X.sheaf
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      have hc : scalarCohomologyCup f F G 0 0 a b =
          (scalarGlobalSectionsEquiv f (F ⊗ G)).symm
            (tmulSection (scalarGlobalSectionsEquiv f F a)
              (scalarGlobalSectionsEquiv f G b)) := by
        apply (scalarCohomologyExtEquiv f (F ⊗ G) 0).injective
        unfold scalarCohomologyCup
        rw [AddEquiv.apply_symm_apply]
        rw [scalarCohomologyExtEquiv_zero_globalSections]
        rw [scalarCohomologyExtEquiv_zero_globalSections,
          scalarCohomologyExtEquiv_zero_globalSections]
        unfold scalarExtCup
        simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀,
          curriedTensor_obj_map, tensorRight, Functor.flip_obj_map,
          curriedTensor_map_app, Category.assoc]
        rw [← tensorHom_def_assoc]
        rw [scalarTensorCoefficient_globalSections_morphism]
        simp only [LinearEquiv.apply_symm_apply]
      rw [hc, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules
