/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.RationalPointTopologicalLocalDimensionBaseChange
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension

/-!
# Local dimension of rational points under field extension

Source: blueprint `lem-ag-group-identity-local-dimension`, first proof paragraph;
Stacks Project, Tags 00P4 and 00OU.
(blueprint: lem-ag-rational-point-local-dimension-base-change)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Local-ring dimension at a rational point is unchanged by extending the ground field.

Source: blueprint `lem-ag-group-identity-local-dimension`, first proof paragraph;
Stacks Project, Tags 00P4 and 00OU.
(blueprint: lem-ag-rational-point-local-dimension-base-change)

Proof: Choose an affine neighbourhood Spec A of the image of p. The structure map makes
A a finite type k-algebra. Its inverse image in the pullback is Spec (A tensor_k K).
The condition on q identifies the contraction of its prime with the prime of p.
Both primes are maximal: the sections give residue fields k and K, respectively.
Tag 00P4 equates the topological dimensions at these primes under scalar extension.
Tag 00OU identifies each with the dimension of the corresponding prime localization.
Finally the affine chart inclusions identify these localizations with the scheme stalks.
This argument permits nilpotents, disconnected schemes, and any field extension; it uses
no smoothness or separatedness. -/
theorem ringKrullDim_rationalPoint_field_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (K : Type u) [Field K] [Algebra k K]
    (q : Spec (.of K) ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hq : q ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _)
    (hqp : q ≫ pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p) :
    ringKrullDim (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
      ringKrullDim ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk
          (q (IsLocalRing.closedPoint K))) := by
  have hleft := ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt f p hp
  calc
    ringKrullDim (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
        topologicalKrullDimAt (p (IsLocalRing.closedPoint k)) :=
      hleft
    _ = topologicalKrullDimAt (q (IsLocalRing.closedPoint K)) :=
      topologicalKrullDimAt_rationalPoint_field_baseChange f p hp K q hq hqp
    _ = ringKrullDim ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk
          (q (IsLocalRing.closedPoint K))) :=
      (ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q hq).symm

end AlgebraicGeometry
