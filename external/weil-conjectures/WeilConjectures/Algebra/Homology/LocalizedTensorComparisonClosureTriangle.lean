/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureTriangleCore

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
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

/-- The localized tensor comparison predicate is closed under triangles.
Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.

Proof: Fix a degree i. The universal derived counit, the canonical tensor associator
and scalar-extension adjunction identify the displayed comparison for a K-flat
representative U with a natural degree-i comparison on D(A). The counit fixes
this map, so changing the derived model conjugates it by canonical isomorphisms.
K-flat quasi-isomorphisms and their roofs give the same conjugation for a change
of representative. Extension from A to C sends A-K-flat complexes to C-K-flat
complexes: tensoring an acyclic C-complex with C tensor_A U is restriction of
that complex tensored over A with U. Thus the target is computed by derived
tensor with N even when A to C is not flat.
Tensoring the distinguished triangle with the K-flat Q and then derived
tensoring over R with B gives a long exact cohomology sequence with its
canonical A tensor_R B action. Flatness of C over this ring makes extension
to C exact, giving the source long exact sequence. Extension from A to C on
K-flat representatives followed by derived tensor with N gives the target
long exact sequence. Naturality of the counit and of the tensor associator,
including compatibility with shifts, makes the degree-wise comparison a
morphism of these sequences. Around degree i at the third vertex, use the
five consecutive terms from vertices 1, 2, 3, 1 shifted, and 2 shifted.
The four outer vertical maps are isomorphisms by the two hypotheses, which
hold in every degree. The five lemma makes the middle map an isomorphism.
Transport through the identifications above gives the stated comparison for
every representative and every model of the third vertex in every degree.
(blueprint: lem-pc-localized-tensor-comparison-closure-triangles). -/
theorem localizedTensorComparisonProperty_closure_triangles
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)),
      T ∈ Pretriangulated.distinguishedTriangles →
      localizedTensorComparisonProperty R A B C Q N t T.obj₁ →
      localizedTensorComparisonProperty R A B C Q N t T.obj₂ →
      localizedTensorComparisonProperty R A B C Q N t T.obj₃ := by
  intro T hT h1 h2 U hU hUK mU i
  exact localizedTensorComparisonProperty_triangle_core R A B C Q N t hC hQ T hT h1 h2 U hU hUK mU i

end ModuleCat
