/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore

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

/-- The localized tensor comparison predicate is closed under retracts.
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
Apply the source and target degree-i functors to the inclusion X to Y and
retraction Y to X. They still compose to identities. Naturality makes the
comparison arrow of X a retract, in the arrow category of C-modules, of that
of Y. If a is the latter comparison and b the former, an inverse of b is
the target inclusion followed by the inverse of a followed by the source
retraction. The two naturality squares and the retract identities show that
both composites are identities. Thus b is an isomorphism whenever a is.
Transport through the identifications above proves the assertion for all
K-flat representatives, all models and all degrees. This argument includes
zero objects and identity retracts; no invertibility of t is assumed.
(blueprint: lem-pc-localized-tensor-comparison-closure-retracts). -/
theorem localizedTensorComparisonProperty_closure_retracts
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {X Y : DerivedCategory (ModuleCat.{u} A)}, Retract X Y →
      localizedTensorComparisonProperty R A B C Q N t Y →
      localizedTensorComparisonProperty R A B C Q N t X := by
  intro X Y hXY hY
  exact localizedTensorComparisonProperty_retract_core R A B C Q N t hQ hXY hY

end ModuleCat
