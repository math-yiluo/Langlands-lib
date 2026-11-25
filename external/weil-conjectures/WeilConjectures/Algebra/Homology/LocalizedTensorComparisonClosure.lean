/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureTriangle
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetract

/-! # Closure of the localized tensor comparison predicate

Source: Stacks Project, Tag 0DJA(1), using Tags 0BYJ and 09PB.
(blueprint: lem-pc-localized-tensor-comparison-closure).
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

/-- The comparison predicate is closed under coproducts, triangles and retracts.
Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.

Proof: the mixed-ring K-flat associator identifies the source comparison for
U tensor_A Q with tensoring the derived base-coefficient comparison by U.
Derived tensor, restriction of scalars and cohomology commute with arbitrary
set-indexed direct sums of module complexes. Scalar extension to C commutes
with sums as a left adjoint. Hence the comparison of a coproduct is a direct
sum of the comparisons of its summands, and is invertible when all of them are.
For a distinguished triangle in D(A), tensor with the A-K-flat Q and then
apply R-to-B derived tensor. This yields the source long exact cohomology
sequence, with its canonical A tensor_R B action. Flatness of C over that ring
makes scalar extension exact, so it preserves this long exact sequence.
The target sequence is obtained by derived tensoring with N over C after
A-to-C scalar extension; K-flat representatives compute this functor. The
mixed associator and naturality of the derived counit give a morphism of these
long exact sequences, including the connecting maps. In every degree the
five lemma makes the third comparison invertible when the first two are.
For a retract, functoriality makes each comparison arrow a retract of the
corresponding comparison arrow for the larger object. A retract of an
isomorphism is an isomorphism. Naturality and invariance under roofs of
K-flat quasi-isomorphisms prove all assertions for every representative and
every model in the definition. Neither the initial comparison for Q nor any
map t is assumed a quasi-isomorphism in this closure assertion. Empty sums,
zero rings, arbitrary unbounded complexes and nonflat A-to-C maps are included.
(blueprint: lem-pc-localized-tensor-comparison-closure). -/
theorem localizedTensorComparisonProperty_closure
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    let P := localizedTensorComparisonProperty R A B C Q N t
    (∀ {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i : I, G i ⟶ S),
      CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι) →
      (∀ i : I, P (G i)) → P S) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)),
      T ∈ Pretriangulated.distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
    (∀ {X Y : DerivedCategory (ModuleCat.{u} A)}, Retract X Y → P Y → P X) := by
  dsimp
  exact ⟨localizedTensorComparisonProperty_closure_coproducts R A B C Q N t hQ,
    localizedTensorComparisonProperty_closure_triangles R A B C Q N t hC hQ,
    localizedTensorComparisonProperty_closure_retracts R A B C Q N t hQ⟩

end ModuleCat
