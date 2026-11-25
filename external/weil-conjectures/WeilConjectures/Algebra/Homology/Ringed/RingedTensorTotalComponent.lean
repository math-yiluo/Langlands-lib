/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation

/-! # Components of the canonical total tensor comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

/-- The canonical total tensor comparison on a single coproduct summand.

Proof: its total map is the coproduct descent of the inverse ordinary tensor
comparison in each bidegree. Precomposition with the summand inclusion is the
corresponding component by the coproduct descent equation.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, total-complex construction.
(blueprint: lem-weil-pbc-ringed-tensor-total-component). -/
theorem ringedTensorTotalComponent {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B)
    (P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)) ℤ)
    (i j n : ℤ) (hij : i + j = n) :
    CochainComplex.ιMapBifunctor
        ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P)
        ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q)
        (@MonoidalCategory.curriedTensor _ _ (monoidalCategory B.ring)) i j n hij ≫
      (e.ordinaryTensor.totalIso A.ring B.ring e.inverseRing e.inverse e.algebraic
        e.ringMap e.pullback e.object_eq e.pushforward e.moduleAdjunction P Q).hom.f n =
    (e.ordinaryTensor.mu (P.X i) (Q.X j)).inv ≫
      e.pullback.map (CochainComplex.ιMapBifunctor P Q
        (@MonoidalCategory.curriedTensor _ _ (monoidalCategory A.ring)) i j n hij) := by
  let := monoidalCategory A.ring
  let := monoidalCategory B.ring
  let := ringedTensorPreadditive A.ring
  let := ringedTensorPreadditive B.ring
  simp only [CanonicalRingedTensorComparison.totalIso, asIso_hom,
    CanonicalRingedTensorComparison.total, tensorPullbackTotal,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc]

end SheafOfModules
