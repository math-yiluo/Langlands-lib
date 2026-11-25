/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ScalarCupZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.ScalarPullbackZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Degree-zero external cup on ordinary sections

Source: Stacks Project, Cohomology, Tags 01DZ, 01F7, 0FKV; Varieties, Tag 0BED.
(blueprint: lem-sc-external-cup-zero-global-sections).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero external cup is the tensor of the two pulled-back sections.
Source: Stacks Project, Cohomology, Tags 01DZ, 01F7, 0FKV; Varieties, Tag 0BED.
(blueprint: lem-sc-external-cup-zero-global-sections).

Proof: The canonical right-derived degree-zero comparison identifies a
cohomology class with its global section. The injective-resolution comparison
with Ext in degree zero is evaluation at 1 of a morphism from the structure
sheaf; restricting scalars identifies this with evaluation of a morphism from
the constant scalar unit. Under these comparisons exact inverse image on
scalar sheaves and the coefficient map adjoint to the tensor-pullback unit send
a section to tensorPullbackTopSection. The degree-zero Yoneda cup is the tensor
of the two morphisms from the unit, composed with the unit inverse. Evaluation
therefore gives the pure tensor of their sections. The scalar tensor coefficient
sends that tensor to tmulSection by its defining characterization. Apply these
facts to the two projection pullbacks. The equality of their structure maps is
the pullback square condition, and the composite is precisely externalCup.
This calculation needs no affine, quasi-compact or quasi-coherent hypothesis;
it also holds for empty schemes and zero sections. -/
theorem externalCup_zero_globalSections
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (a : scalarCohomology f F 0) (b : scalarCohomology g G 0) :
    scalarGlobalSectionsEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (externalCup f g F G 0 0 a b) =
      externalGlobalSectionsTensor f g F G
        (scalarGlobalSectionsEquiv f F a ⊗ₜ[k] scalarGlobalSectionsEquiv g G b) := by
  unfold externalCup
  rw [scalarCohomologyCup_zero_globalSections,
    scalarCohomologyPullback_zero_globalSections,
    scalarCohomologyPullback_zero_globalSections]
  rfl

end AlgebraicGeometry.Scheme.Modules
