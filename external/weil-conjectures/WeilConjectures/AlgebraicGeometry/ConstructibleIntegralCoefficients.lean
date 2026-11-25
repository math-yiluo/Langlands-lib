/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsForward
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

/-!
# Constructibility of torsion sheaves with integral coefficients

Source: Stacks Project, Tags 03RW and 095E; the comparison of (2) and (3)
for torsion sheaves and the canonical integral module structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A torsion abelian sheaf is constructible as an integral module sheaf exactly
when its underlying sheaf of sets is constructible.

Source: Stacks Project, Definition 03RW (2), (3), Lemma 095E, and the comparison
needed in the retract argument of Lemma 03SD. This comparison is written out here;
03RW does not identify the two notions for nontorsion sheaves.
(blueprint: q1-constructible-integral-coefficients)

Proof: Use the same finite constructible stratification in both directions.
The equivalence from abelian groups to modules over ULift Z preserves constant
sheaves, inverse image, restriction to localized sites, and geometric stalks:
its inverse is the underlying abelian group functor, and these operations are
characterized by their adjunctions or colimits. The forgetful functor to sets
also commutes with these operations, since the algebraic operations on a stalk
or a sheafification are induced from the operations on sections.
On a stratum, a locally constant integral module sheaf thus has locally
constant underlying sets. Its finitely generated stalks are torsion, since
inverse image preserves torsion and stalks commute with the filtered union
of the n-torsion subsheaves. A finitely generated torsion abelian group is
finite: choose finitely many generators, choose a positive annihilator for
each, and map the finite product of the corresponding cyclic groups onto it.
This proves the implication to the underlying set predicate.
Conversely take a stratum with a finite locally constant set sheaf. Refine
its trivializing etale cover near each geometric point to make the group
operations constant as well. Indeed a nonempty trivializing piece has a
finite constant value A (equal to any of its geometric stalks). For each of
the finitely many pairs in A x A, equality of its sum with the corresponding
stalk value holds in some etale neighbourhood; refine by the finite fiber
product of these neighbourhoods. Treat zero and negatives in the same way.
These refinements cover the stratum, and the trivializations now identify
the sheaf with the constant finite abelian group at the chosen point.
Every homomorphism of abelian groups is Z-linear, so these are integral
module trivializations. Finite stalks are finitely generated integral
modules, giving IsFiniteLocallyConstantSheaf on every stratum.
Empty cover members may be discarded, and an empty stratum has no stalk
conditions; the zero sheaf is constant with a one-element underlying set.
For the module predicate's separably closed geometric fields, compare a
point with its extension to an algebraic closure. The extension is purely
inseparable, and finite etale algebras over both fields are split products
with the same factors. Hence lifts of the two points to any etale
neighbourhood correspond, giving identical pointed-neighbourhood colimits
and stalks. Finiteness tested at algebraically closed fields therefore
also gives the required finite, hence finitely generated, stalks at
separably closed fields. Thus the stratification witnesses the module
predicate as well. -/
theorem isConstructibleSheaf_integral_iff {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F) ↔
      IsConstructibleEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) := by
  dsimp
  constructor
  · exact isConstructibleSheaf_integral_forward F hF
  · exact isConstructibleSheaf_integral_backward F hF

end AlgebraicGeometry.Scheme
