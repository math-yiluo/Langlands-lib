/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialExists
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementAugmentation

/-! # Existence of an augmented Godement model -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A single coefficient sheaf has an augmented concrete Godement model.
Source: Stacks Project, Tag 0FKR; Banerjee, arXiv:1004.1491, §1.1.4.
(blueprint: lem-sc-module-cup-godement-model-pairing-models-exist)
Proof: the stalk functor to families of modules has right adjoint given by the
product of stalk skyscrapers. The hom equivalence is the product of the
`skyscraperHomEquiv` equivalences. Its unit is `moduleCup_godementUnit`, its
functorial action is `moduleCup_godementMap`, and its multiplication is
`moduleCup_godementMultiply`: project to the point coordinate and evaluate
its stalk. The two adjunction triangle identities imply the two unit laws,
and naturality of evaluation gives associativity. Set A in degree n to the
(n+1)-fold iterate of this functor on F, insert the unit for cofaces, and
multiplication for codegeneracies. The monad laws and naturality give the
cosimplicial relations, hence define A on every simplex map by its unique
order-preserving surjection/injection factorization. The recursive insertion
and collapse formulas are exactly its cofaces and codegeneracies. The germ
map into A in degree zero is killed by the alternating first differential,
since its two composites are equal by naturality of the unit. It therefore
defines the augmentation from F[0], with all other components zero. Extension
by zero and the single-object isomorphism give the stated augmentation
identity. This construction applies to empty schemes (empty products) and to
zero sheaves without additional choices. -/
theorem moduleCup_godement_models_exist (X : Scheme.{u}) (F : X.Modules) :
    ∃ (A : CosimplicialObject X.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        (((alternatingCofaceMapComplex X.Modules).obj A).extend
          ComplexShape.embeddingUpNat)),
      ModuleCupGodementModel X F A a ∧ ModuleCupGodementCodegeneracies X F A := by
  obtain ⟨A, h, hδ, hσ⟩ := moduleCup_godement_cosimplicial_exists X F
  obtain ⟨a, ha⟩ := moduleCup_godement_augmentation_exists X F A h hδ
  exact ⟨A, a, ha, h, hσ⟩

end
end AlgebraicGeometry.Scheme.Modules
