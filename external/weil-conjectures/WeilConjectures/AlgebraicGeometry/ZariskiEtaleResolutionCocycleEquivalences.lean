/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution

/-! # Additive equivalences for Zariski–étale resolution cocycles

Source: Stacks Project, Section 01FT, equation-cohomology-object-site;
Tag 06XR (1), lemma-compute-ext-resolutions.
(blueprint: lem-weil-pbc-zariski-etale-resolution-cocycle-equivalences)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Evaluate the natural resolution comparison, remove its universe lifts, and use
exactness of evaluation to commute evaluation with homology. -/
private theorem objectResolutionEquiv.{v, w, t}
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{t} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) (I : InjectiveResolution F)
    (q : ℕ) (V : C) :
    Nonempty (Sheaf.H' F q V ≃+
      (((sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V)).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex).homology q) := by
  let K := ((sheafToPresheaf J AddCommGrpCat.{w}).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V)
  obtain ⟨e⟩ := objectCohomologyPresheaf_resolution J F I q
  let a := (e.app (op V)).addCommGroupIsoToAddEquiv
  let h := (K.sc q).mapHomologyIso E
  exact ⟨(AddEquiv.ulift.symm.trans a).trans
    (AddEquiv.ulift.trans h.symm.addCommGroupIsoToAddEquiv)⟩

-- The unchanged statement includes an unused comparison map and existential names.
set_option linter.unusedVariables false in
/-- Intermediate cocycle-comparison component for the Zariski–étale resolution comparison.

The existence of the displayed additive equivalences is the termwise sheafification,
free-abelian, and Yoneda calculation from Stacks Project, Section 01FT.
(blueprint: lem-weil-pbc-zariski-etale-resolution-cocycle-equivalences)

Proof: evaluate objectCohomologyPresheaf_resolution at V and remove both universe
lifts using AddEquiv.ulift. Exact evaluation identifies the resulting presheaf
homology with homology of the evaluated resolution. This gives e₁ for R on the
Zariski site and e₂ for I at i(V) on the étale site. Evaluation of continuous
pushforward at V is definitionally evaluation at i(V), in every degree and for
every differential, so e₂ has precisely the required target. The map b is
irrelevant to the existence of these equivalences. -/
theorem zariski_etale_resolution_cocycle_equivalences
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (q : ℕ) (V : X.Opens) :
    ∃ (e₁ : Sheaf.H' ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) q V ≃+
        ↑(HomologicalComplex.homology
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).obj R.cocomplex) q))
      (e₂ : Sheaf.H' F q (i.obj V) ≃+
        ↑(HomologicalComplex.homology
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).obj
                (((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                  (Opens.grothendieckTopology X.carrier)
                    X.smallEtaleTopology).mapHomologicalComplex
                       (ComplexShape.up ℕ)).obj I.cocomplex)) q)), True := by
  obtain ⟨e₁⟩ := objectResolutionEquiv
    (Opens.grothendieckTopology X.carrier) _ R q V
  obtain ⟨e₂⟩ := objectResolutionEquiv X.smallEtaleTopology F I q (i.obj V)
  exact ⟨e₁, e₂, trivial⟩
