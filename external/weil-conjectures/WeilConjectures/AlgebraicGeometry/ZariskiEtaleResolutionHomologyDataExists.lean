/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionCocycleHomology
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionPullbackCocycle

/-! # Resolution comparison bridge -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

private noncomputable def resolutionSectionEquiv
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    (A : Sheaf J AddCommGrpCat.{u + 1}) :
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) ≃ A.obj.obj (op V) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ A).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) A.obj).trans yonedaEquiv)

private lemma resolutionSectionEquiv_comp
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    {A B : Sheaf J AddCommGrpCat.{u + 1}}
    (a : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) (f : A ⟶ B) :
    resolutionSectionEquiv J V B (a ≫ f) =
      (f.hom.app (op V)).hom (resolutionSectionEquiv J V A a) := by
  rfl

private lemma resolutionSectionEquiv_zero
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    (A : Sheaf J AddCommGrpCat.{u + 1}) :
    resolutionSectionEquiv J V A 0 = 0 := by
  rfl

/-- The canonical pullback-counit map is represented by any augmented comparison.

Source: Stacks Project, Cohomology, Tag 01FB; Derived Categories, Tags 013P and
015B (4); Cohomology on Sites, Tags 0730 and 0733 (1).
(blueprint: lem-zariski-etale-resolution-homology-data-exists)

Proof: Let P(V) be the sheafification of the free abelian presheaf on yoneda(V).
The sheafification adjunction, the free abelian group adjunction and additive Yoneda
identify Hom(P(V), A) with A(V), naturally in A. Applied termwise to R, this
identifies the Hom complex computing Ext(P(V), i_*F, q) with the section complex
R(V). The injective resolution computation of Ext gives e₁. The same construction
for I at i(V) gives e₂, since evaluating i_*I at V is evaluating I at i(V).
These additive identifications are valid also for q = 0, the zero sheaf and empty V;
if the Ext universe differs, use the canonical change-of-universe equivalence.

For an arbitrary coefficient A, resolve A and i⁻¹A. Exactness of inverse image
implies that direct image preserves injective objects. Extend the unit of the
adjunction to a comparison from the first resolution to the direct image of the
second, using the degree-by-degree extension through injective objects. Two such
comparisons are homotopic, by factoring their difference through the differentials.
Naturality of these lifts and the horseshoe construction therefore give a family
on section homology natural in A and commuting with connecting homomorphisms.
In degree zero it is evaluation of the unit. Ext(P(V), -, q) is effaceable for
q > 0, so dimension shifting identifies this family with the supplied fstar:
embed A into an injective, use the surjective connecting map, and induct on q.

Now take A = i_*F and follow the unit comparison with the comparison for the counit
into I. Naturality of the Ext-to-section identifications computes the composite
as fstar followed by cohomology of the counit. The adjunction triangle identity
says its augmentation is the pushed augmentation of F into I. The difference from
the prescribed b is null-homotopic (the theorem
zariski_etale_resolution_homology_independent). Evaluation preserves the homotopy,
so their homology maps agree. This proves the formula using the e₁ and e₂ already
constructed, for every x. We claim no compatibility for arbitrary equivalences.
This theorem does not assert the existence of an augmented chain map. -/
theorem zariski_etale_resolution_homology_data_exists
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)]
    (fstar : ∀ (p : ℕ) (V : X.Opens)
      (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}),
      Sheaf.H' A p V ⟶
        Sheaf.H' ((sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj A)
          p (i.obj V))
    (hfstar : (∀ (p : ℕ) (V : X.Opens) (A A' : Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u + 1}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p).map φ).app
          (op V) ≫
            fstar p V A' =
          fstar p V A ≫
            ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology p).map
              ((sheafPullback i AddCommGrpCat.{u + 1}
                (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map φ)).app
                  (op (i.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}))
        (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)).ShortExact)
        (p : ℕ) (V : X.Opens) (x : Sheaf.H' S.X₃ p V),
        (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : X.Opens) (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})
        (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)).hom.app (op (i.obj V))).hom
            (((toSheafify X.smallEtaleTopology
              (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (i.obj V)))) =
          (((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).unit.app A).hom.app
              (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify (Opens.grothendieckTopology X.carrier)
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V))))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (hb : R.ι.f 0 ≫ b.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map (I.ι.f 0))
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
                       (ComplexShape.up ℕ)).obj I.cocomplex)) q)),
      ∀ x, e₂ ((fstar q V
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj V))).hom x) =
        (HomologicalComplex.homologyMap
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).map b) q).hom (e₁ x) := by
  obtain ⟨e₁, e₂, he⟩ :=
    zariski_etale_resolution_cocycle_homology i hi F I R b q V
  refine ⟨e₁, e₂, ?_⟩
  intro x
  obtain ⟨a, ha, rfl⟩ := R.extMk_surjective x (q + 1) rfl
  let J := Opens.grothendieckTopology X.carrier
  let K := X.smallEtaleTopology
  let s := resolutionSectionEquiv J V (R.cocomplex.X q) a
  let c := (resolutionSectionEquiv K (i.obj V) (I.cocomplex.X q)).symm
    ((b.f q).hom.app (op V) s)
  have hsec : (b.f q).hom.app (op V) s =
      resolutionSectionEquiv K (i.obj V) (I.cocomplex.X q) c := by
    exact (Equiv.apply_symm_apply _ _).symm
  have hc : c ≫ I.cocomplex.d q (q + 1) = 0 := by
    apply (resolutionSectionEquiv K (i.obj V) (I.cocomplex.X (q + 1))).injective
    rw [resolutionSectionEquiv_comp, ← hsec, resolutionSectionEquiv_zero]
    have hcomm := congrArg
      (fun f ↦ (f.hom.app (op V)).hom s) (b.comm q (q + 1))
    have hz : (R.cocomplex.d q (q + 1)).hom.app (op V) s = 0 := by
      change resolutionSectionEquiv J V (R.cocomplex.X (q + 1))
        (a ≫ R.cocomplex.d q (q + 1)) = 0
      rw [ha, resolutionSectionEquiv_zero]
    change (I.cocomplex.d q (q + 1)).hom.app (op (i.obj V))
        ((b.f q).hom.app (op V) s) =
      (b.f (q + 1)).hom.app (op V)
        ((R.cocomplex.d q (q + 1)).hom.app (op V) s) at hcomm
    rw [hz, map_zero] at hcomm
    exact hcomm
  have hclass := zariski_etale_resolution_pullback_cocycle
    i hi fstar hfstar F I R b hb q V a ha c hc hsec
  rw [hclass]
  exact he a ha c hc hsec
