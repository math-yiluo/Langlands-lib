/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Comparison of constant etale cohomology along an isomorphism

Source: Stacks Project, Cohomology on Sites, the derived-functor definition of cohomology;
Etale Cohomology, Lemma 09ZC, implicit transport in the affine reduction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Vanishing of derived constant etale cohomology agrees with vanishing of the
Ext-defined sheaf cohomology on an isomorphic scheme. No finiteness, affineness,
normality, or separably closed field hypothesis is needed.

Source: Stacks Project, Cohomology on Sites, definition of cohomology as derived global
sections; Etale Cohomology, Lemma 09ZC, first sentence and implicit transport.

Proof: Composition with a scheme isomorphism gives inverse equivalences of the small
etale sites, preserving coverings and terminal objects. The induced equivalence of
abelian sheaves is exact, preserves injectives and global sections, and identifies
constant sheaves by the sheafification universal property. It therefore induces an
additive isomorphism on all cohomology groups. To compare the two cohomology definitions,
resolve the sheaf by injectives in nonnegative degrees. This bounded below injective
complex is K-injective. Both the total right derived global sections on the single
complex and the classical right derived functors are computed by its global sections.
The latter compute Ext from the constant free abelian sheaf, since Hom from that sheaf
is global sections. Their degree `n` groups are thus additively isomorphic to `Sheaf.H`.
An abelian group object is zero exactly when its underlying type is a subsingleton.
This includes degree zero and the empty scheme.
(blueprint: lem-weil-pbc-constant-etale-cohomology-iso-comparison)
-/
theorem isZero_constant_cohomology_iff_subsingleton_H_of_iso
    (X Y : Scheme.{u}) (e : X ≅ Y)
    (M : Type (u + 1)) [AddCommGroup M] (n : ℕ) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} X (n : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) ↔
      Subsingleton (Sheaf.H.{u + 1}
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)) n) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  let c := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} e.inv).app
    (AddCommGrpCat.of M)
  let cH := ((Sheaf.functorH.{u + 1} Y.smallEtaleTopology n).mapIso c).addCommGroupIsoToAddEquiv
  let eH := (cohomologyEquiv e.inv F n).trans cH
  obtain ⟨a⟩ := Scheme.nonempty_sheafH_extDerivedIso X n
  constructor
  · intro hz
    have hx : Subsingleton (Sheaf.H.{u + 1} F n) :=
      AddCommGrpCat.subsingleton_of_isZero (hz.of_iso (a.app F))
    exact @Equiv.subsingleton _ _ eH.symm.toEquiv hx
  · intro hy
    have hx : Subsingleton (Sheaf.H.{u + 1} F n) :=
      @Equiv.subsingleton _ _ eH.toEquiv hy
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr hx).of_iso (a.app F).symm

end AlgebraicGeometry.Etale
