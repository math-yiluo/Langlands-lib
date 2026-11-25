/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Pullback preserves finite-stalk constructibility

Source: finite pushforward constructibility blueprint, step 1; Stacks Project, Tag 095A.
(blueprint: lem-weil-pbc-constructible-etale-set-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback of an abelian etale sheaf preserves constructibility of its underlying
set sheaf, including the finiteness of its geometric stalks.

Source: blueprint `lemma-detection-proper-direct-image--1`, step 1;
Stacks Project, Tag 095A.
(blueprint: lem-weil-pbc-constructible-etale-set-pullback).

Proof: Choose a finite constructible lisse stratification of the underlying set sheaf.
Pull back the strata along g using `Stratification.pullback`. Preimages of constructible
subsets are constructible and preimages of locally closed subsets are locally closed;
the strata still form a disjoint finite covering. On each pulled-back stratum, use the
composition isomorphisms for set inverse image and the Cartesian square to identify the
restriction with inverse image of the original lisse restriction. A trivializing etale
cover pulls back to a trivializing etale cover, and inverse image of a constant sheaf is
constant. At a geometric point the inverse-image stalk is the original stalk at the
composite point, so it remains finite. Thus the pulled-back stratification is lisse.
Finally `etaleInverseImageAlgebraicStructures` identifies set inverse image with the
underlying set sheaf of abelian inverse image. Transport the lisse strata across this
isomorphism. This uses finite stalks, not merely finitely generated abelian stalks. -/
theorem isConstructibleEtaleSheafOfSets_upperStar
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E)) := by
  obtain ⟨S, hS⟩ := hE
  refine ⟨S.pullback g, ?_⟩
  exact finiteLocallyConstant_pullback_stratum g E S hS

end AlgebraicGeometry.Scheme
