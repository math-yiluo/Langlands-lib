/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonUnit
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonShift

/-! # The generators satisfy localized tensor comparison

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-generators).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The comparison predicate contains every shift of the free rank-one generator.
Source: Stacks Project, Tags 0DJA(1) and 0BYJ.

Proof: for U=A[0], the unitors identify U tensor Q with Q, and the scalar-extension
unit identifies F(U) with C[0]. Naturality of the universal derived counit and
localized_eq identify the comparison with the given comparison for Q. For A[n]
the shift-tensor isomorphisms reindex the comparison by n, so the hypothesis in
every degree proves the assertion. ULift A is canonically A-linearly isomorphic
to A. Finally, a K-flat representative U of the shifted generator computes the
same derived tensor as that generator: represent the derived isomorphism by a
roof and resolve its apex by an A-K-flat complex. K-flat scalar extension and
tensoring with the A-K-flat Q preserve both roof legs. Universality of the
R-to-B derived counit identifies the base-derived cohomology models, including
their A tensor B actions; tensoring their homology isomorphisms with C and using
the natural localized comparison squares proves the condition for every mU.
Thus the predicate's universal quantification over representatives holds. The
argument allows arbitrary shifts, unbounded Q and N, and zero rings.
(blueprint: lem-pc-localized-tensor-comparison-generators). -/
theorem localizedTensorComparisonProperty_generators
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (m : BaseDerivedTensorCohomologyModel R A B Q C)
    (h : ∀ i : ℤ, IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)) :
    ∀ n : ℤ, localizedTensorComparisonProperty R A B C Q N t
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (ULift.{0} A)))⟦n⟧) := by
  have hunit := localizedTensorComparisonProperty_unit R A B C Q N t hQ m h
  intro n
  exact localizedTensorComparisonProperty_shift R A B C Q N t _ hunit n

end ModuleCat
