/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution

/-! # Object cohomology stalks and section complexes

Source: Stacks Project, Cohomology on Sites, Tag 03F3; Etale Cohomology, Tag 09AX.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Evaluate an etale sheaf on the given open objects and take its Zariski stalk. 
(blueprint: lem-weil-pbc-etale-object-cohomology-stalk-complex)
-/
noncomputable abbrev etaleObjectStalkSections
    (X : Scheme.{u + 1}) (i : X.Opens ⥤ X.Etale) (x : X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙
        colim

instance (X : Scheme.{u + 1}) (i : X.Opens ⥤ X.Etale) (x : X) :
    (etaleObjectStalkSections X i x).Additive := inferInstance

/-- Object cohomology at a Zariski stalk is the homology of stalkwise sections of
an injective resolution. This does not assume strict henselianity.
Source: Stacks Project, Cohomology on Sites, Tag 03F3; Etale Cohomology, Tags 03XA and 09AX,
second and third sentences of the proof.
(blueprint: lem-weil-pbc-etale-object-cohomology-stalk-complex)

Proof: The site admits a dense small subsite of size u+1. Choose affine opens
of X, then affine etale schemes of finite presentation over these opens, with
algebras encoded by finite presentations over their coordinate rings. There are
only u+1-small sets of such presentations and of their morphisms. These objects
cover every etale object, and every cover of an affine object refines to a finite
affine etale cover (03XA). Sheaves are therefore equivalent to sheaves on this
small subsite. The latter category with coefficients of size u+1 is Grothendieck
abelian and has enough injectives. Transport an injective resolution of F back
along this equivalence; call it I. This avoids presuming that the entire category
of etale objects is essentially small in u+1.

The free abelian sheaf on the representable i(U) corepresents evaluation at i(U),
by sheafification, the free-abelian adjunction and Yoneda. Apply this additive
identification in every degree of I: Ext from the representable is homology of
its evaluation complex, naturally in U. The opposite neighbourhood category is
filtered. Filtered colimits of abelian groups are exact and commute with homology.
Taking colimits of the natural identifications gives the stated additive
bijection. Compute Ext first in the sheaf morphism universe using I, then compare
with the supplied HasExt universe using the universe-independence of Ext.
Lift the value groups to a common universe when taking the left colimit;
AddCommGrpCat.uliftFunctor preserves colimits and homology, and AddEquiv.ulift
removes that lift from the right side. No coefficient-universe change for sheaves
is required. The theorem holds for arbitrary i: only evaluation and its
functoriality are used. Empty schemes have no x; q=0 is included. -/
theorem etaleObjectCohomology_stalk_complex
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : X) :
    ∃ I : InjectiveResolution F,
      Nonempty
        (↑(colimit
          (((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙
            Sheaf.cohomologyPresheaf F q ⋙ AddCommGrpCat.uliftFunctor.{u + 2, w})) ≃+
          (((etaleObjectStalkSections X i x).mapHomologicalComplex (.up ℕ)).obj
            I.cocomplex).homology q) := by
  classical
  let I := injectiveResolution F
  let K := ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let R := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
    ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙ colim
  obtain ⟨e⟩ := objectCohomologyPresheaf_resolution X.smallEtaleTopology F I q
  refine ⟨I, ?_⟩
  let N := ((OpenNhds.inclusion
    (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op
  let d := colim.mapIso (Functor.isoWhiskerLeft N e)
  let h := (K.sc q).mapHomologyIso R
  let t := d ≪≫ (preservesColimitIso AddCommGrpCat.uliftFunctor (N ⋙ K.homology q)).symm
  let z := t ≪≫ AddCommGrpCat.uliftFunctor.mapIso h.symm
  exact ⟨z.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩
