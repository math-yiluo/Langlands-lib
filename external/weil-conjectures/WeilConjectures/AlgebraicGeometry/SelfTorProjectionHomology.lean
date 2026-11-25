/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses
import WeilConjectures.AlgebraicGeometry.SelfTorProjectionHomologyTermwise
import WeilConjectures.Topology.ClosedImmersionPushforwardExact

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Projection-formula and representative-comparison step for self-Tor.

This is the intermediate statement used to separate the qcqs projection formula
from the final choice of the literal termwise pullback representative.  Its
proof is the derived projection formula, exactness of closed-immersion
pushforward, and transport along the displayed complex isomorphism.
(blueprint: lem-pc-self-tor-projection-homology). -/
theorem nonempty_selfTor_projection_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (k : ℤ) (Q : CochainComplex Z.Modules ℤ)
    (e : Q ≅ ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj (S.obj B ⊗ S.obj B)) ≅
      (Scheme.Modules.pushforward i).obj (Q.homology k)) := by
  dsimp
  obtain ⟨h⟩ := nonempty_selfTor_projection_homology_termwise i P a hP k
  let eH := HomologicalComplex.homologyMapIso e k
  exact ⟨h ≪≫ (Scheme.Modules.pushforward i).mapIso eH.symm⟩

end AlgebraicGeometry
