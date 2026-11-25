/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed

/-! # Finite qcqs open-closed trees and their actual branch functors

## References

* Stacks Tag 09AH, iterated
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite rooted binary scheme tree. Each split has complementary open and closed
children; both edges are quasi-compact, and each vertex is qcqs. The inductive type
includes one-vertex trees and empty schemes. -/
inductive QcqsOpenClosedTree : Scheme.{u} → Type (u + 1)
  | leaf (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
      QcqsOpenClosedTree X
  | split {X U Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
      [QuasiCompact j] [QuasiCompact i]
      (complement : Set.range j.base = (Set.range i.base)ᶜ)
      (openTree : QcqsOpenClosedTree U) (closedTree : QcqsOpenClosedTree Z) :
      QcqsOpenClosedTree X

namespace QcqsOpenClosedTree

/-- A vertex with its unique path to the root, retaining the actual scheme morphisms. -/
inductive Path : {X : Scheme.{u}} → QcqsOpenClosedTree X → Scheme.{u} → Type (u + 1)
  | root {X : Scheme.{u}} (t : QcqsOpenClosedTree X) : Path t X
  | openBranch {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
      [QuasiCompact j] [QuasiCompact i]
      (h : Set.range j.base = (Set.range i.base)ᶜ)
      (a : QcqsOpenClosedTree U) (b : QcqsOpenClosedTree Z) (p : Path a W) :
      Path (.split j i h a b) W
  | closedBranch {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
      [QuasiCompact j] [QuasiCompact i]
      (h : Set.range j.base = (Set.range i.base)ᶜ)
      (a : QcqsOpenClosedTree U) (b : QcqsOpenClosedTree Z) (p : Path b W) :
      Path (.split j i h a b) W

/-- The scheme morphism along a path, composed in the direction towards the root. -/
def Path.toRoot {X W : Scheme.{u}} {t : QcqsOpenClosedTree X} (p : Path t W) : W ⟶ X :=
  match X, t, W, p with
  | _, _, _, .root _ => 𝟙 _
  | _, _, _, @Path.openBranch _ _ _ _ _ _ j i _ _ _ _ _ _ _ p => p.toRoot ≫ j
  | _, _, _, @Path.closedBranch _ _ _ _ _ _ j i _ _ _ _ _ _ _ p => p.toRoot ≫ i

/-- A path ends at a leaf precisely when its terminal subtree is a one-vertex tree. -/
def Path.IsLeaf {X W : Scheme.{u}} {t : QcqsOpenClosedTree X} (p : Path t W) : Prop :=
  match X, t, W, p with
  | _, _, _, @Path.root _ (@QcqsOpenClosedTree.leaf _ _ _) => True
  | _, _, _, @Path.root _ (@QcqsOpenClosedTree.split _ _ _ _ _ _ _ _ _ _ _ _ _ _) => False
  | _, _, _, @Path.openBranch _ _ _ _ _ _ j i _ _ _ _ _ _ _ p => p.IsLeaf
  | _, _, _, @Path.closedBranch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p => p.IsLeaf

/-- The path functor is the actual composite of open extension by zero and closed
module direct image. At the root it is the identity, with no choice of functors. -/
def Path.extension
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X W : Scheme.{u}} {t : QcqsOpenClosedTree X} (p : Path t W) :
    Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj R W) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X) :=
  match X, t, W, p with
  | _, _, _, .root _ => 𝟭 _
  | _, _, _, @Path.openBranch _ _ _ _ _ _ j i _ _ _ _ _ _ _ p =>
      p.extension R ⋙ CondensedRing.openImmersionLowerShriek R j
  | _, _, _, @Path.closedBranch _ _ _ _ _ _ j i _ _ _ _ _ _ _ p =>
      p.extension R ⋙ CondensedRing.lowerStar R i

end QcqsOpenClosedTree
end AlgebraicGeometry.ProEtale
