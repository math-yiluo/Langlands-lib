/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Source.SourceLocalizedCocycleHomology

/-! # Restriction of a cocycle through exact strict-local functors

Source: Stacks Project, Tags 03Q9 and 03QO, restriction and exact global sections.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.SourceCocycleExactRestriction.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exactHomologyProjection
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : CochainComplex A ℤ) (n : ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj L).homologyπ n ≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L =
    ((L.sc n).mapCyclesIso F).hom ≫ F.map (L.homologyπ n) := by
  dsimp [Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso,
    HomologicalComplex.homologyFunctorIso, ShortComplex.homologyFunctorIso]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]
  simp only [ShortComplex.homologyMap_id, Category.id_comp]
  rw [(L.sc n).leftHomologyData.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ShortComplex.LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv]
  rw [← Category.assoc]
  erw [((L.sc n).leftHomologyData.map F).homologyπ_comp_homologyIso_hom]
  dsimp only [ShortComplex.LeftHomologyData.map_π]
  rw [Category.assoc, ← F.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation and restriction of a single-source cocycle commute with the homology
comparisons for exact inverse image and exact strict-local sections. This assertion
concerns complexes and their homology only, before localization or transport to a
specified derived object.

Source: Stacks Project, Tags 03Q9 (restriction of an injective complex) and 03QO
(exactness of strict-local sections).
(blueprint: lem-weil-pbc-source-cocycle-exact-restriction).

Proof: the inverse of leftHomologyData.homologyIso sends the cohomology class of the
cocycle to its homology class in the Hom complex. Degreewise free-generator evaluation
sends this cycle to the section represented by f. Factor f through L.cycles n.
Naturality of tau for the cycle inclusion says that its image is the cycle obtained
by applying inverse image and global sections. Naturality for the homology projection
then identifies its homology class with tau applied to the section of L.homology n.
The exact-functor homology isomorphisms identify the mapped cycle inclusions and
projections with those of the mapped complexes. Apply these first to global sections
and then to inverse image. This gives the stated composite. Boundaries are killed by
the homology projection, so the computation descends to cohomology classes. Zero
cycles, zero complexes and negative degrees use the identical projection calculation. -/
private theorem sourceSectionsCocycleRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (n : ℤ) (W : S.Etale)
    (τ : (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1})
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    letI := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let c := CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
    let x := ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      (smallModel_sourceFreeSectionsComplexIso W L).hom)
        ((leftHomologyData
          ((CochainComplex.singleFunctor _ 0).obj
            ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.inv c)
    (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map a ≫
      (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app C ≫
      G.map ((U.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L)) x) =
      τ.app (L.homology n)
        (smallModel_sourceFreeSectionsEquiv W _
          (L.liftCycles f (n + 1) (by simp) hf ≫ L.homologyπ n)) := by
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
  let C := (U.mapHomologicalComplex (.up ℤ)).obj L
  let D := (G.mapHomologicalComplex (.up ℤ)).obj C
  let A := ((CochainComplex.singleFunctor _ 0).obj
    ((strictLocalFreeSheaf S.smallEtaleTopology).obj W))
  let X := HomComplex A L
  let h := leftHomologyData A L n
  let q := Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf
  let e := (smallModel_sourceFreeSectionsComplexIso W L).hom
  let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
  let ψ : X ⟶ D := e ≫ a
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
  let k := ((C.sc n).mapCyclesIso G).hom ≫ G.map ((L.sc n).mapCyclesIso U).hom
  let z := h.cyclesIso.inv q
  have hz : h.homologyIso.inv (CohomologyClass.mk q) = X.homologyπ n z := by
    exact ConcreteCategory.congr_hom h.π_comp_homologyIso_inv q
  have hM : X.homologyπ n ≫ H.map e ≫ H.map a ≫
      (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app C ≫
        G.map ((U.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L) =
      HomologicalComplex.cyclesMap ψ n ≫ k ≫ G.map (U.map (L.homologyπ n)) := by
    rw [← Category.assoc (H.map e) (H.map a), ← H.map_comp]
    erw [HomologicalComplex.homologyπ_naturality_assoc]
    erw [← Category.assoc (D.homologyπ n)
      ((G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app C)]
    erw [exactHomologyProjection G C n]
    simp only [Category.assoc, ← G.map_comp]
    erw [exactHomologyProjection U L n]
    simp only [G.map_comp]
    rfl
  have hk : k (HomologicalComplex.cyclesMap ψ n z) =
      τ.app (L.cycles n) (smallModel_sourceFreeSectionsEquiv W _
        (L.liftCycles f (n + 1) (by simp) hf)) := by
    apply (AddCommGrpCat.mono_iff_injective (G.map (U.map (L.iCycles n)))).mp
      (inferInstance : Mono (G.map (U.map (L.iCycles n))))
    have hi : k ≫ G.map (U.map (L.iCycles n)) = D.iCycles n := by
      dsimp only [k]
      rw [Category.assoc, ← G.map_comp]
      erw [(L.sc n).mapCyclesIso_hom_iCycles U]
      exact (C.sc n).mapCyclesIso_hom_iCycles G
    have hz' : X.iCycles n z = (q : Cochain A L n) := by
      exact ConcreteCategory.congr_hom h.cyclesIso_inv_comp_iCycles q
    calc
      (G.map (U.map (L.iCycles n))) (k (HomologicalComplex.cyclesMap ψ n z)) =
          D.iCycles n (HomologicalComplex.cyclesMap ψ n z) :=
        ConcreteCategory.congr_hom hi _
      _ = ψ.f n (X.iCycles n z) :=
        ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) z
      _ = τ.app (L.X n) (smallModel_sourceFreeSectionsEquiv W _ f) := by
        rw [hz']
        change τ.app (L.X n) (smallModel_sourceFreeSectionsEquiv W _
          ((Cochain.fromSingleEquiv (zero_add n))
            (Cochain.fromSingleMk f (zero_add n)))) = _
        rw [Cochain.fromSingleEquiv_fromSingleMk]
      _ = (G.map (U.map (L.iCycles n)))
          (τ.app (L.cycles n) (smallModel_sourceFreeSectionsEquiv W _
            (L.liftCycles f (n + 1) (by simp) hf))) := by
        have ht := τ.naturality (L.iCycles n)
        dsimp only [Functor.comp_map] at ht
        have hv := ConcreteCategory.congr_hom ht (smallModel_sourceFreeSectionsEquiv W _
          (L.liftCycles f (n + 1) (by simp) hf))
        simp only [AddCommGrpCat.comp_apply] at hv
        erw [← smallModel_sourceFreeSectionsEquiv_comp, L.liftCycles_i] at hv
        exact hv
  dsimp only
  change ((H.map e ≫ H.map a ≫
    (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app C ≫
      G.map ((U.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L))
        (h.homologyIso.inv (CohomologyClass.mk q))) = _
  rw [hz]
  erw [← AddCommGrpCat.comp_apply, hM]
  simp only [AddCommGrpCat.comp_apply]
  erw [hk]
  have ht := τ.naturality (L.homologyπ n)
  dsimp only [Functor.comp_map] at ht
  rw [smallModel_sourceFreeSectionsEquiv_comp]
  exact (ConcreteCategory.congr_hom ht _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exactHomologyTransport
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : CochainComplex A ℤ) (Y : DerivedCategory A)
    (t : DerivedCategory.Q.obj L ⟶ Y) (n : ℤ) :
    (DerivedCategory.homologyFunctorFactors B n).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
      (DerivedCategory.homologyFunctor B n).map
        (F.mapDerivedCategoryFactors.inv.app L ≫ F.mapDerivedCategory.map t) ≫
      (F.mapDerivedCategoryHomologyFunctorIso n).inv.app Y =
    (F.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L ≫
      F.map ((DerivedCategory.homologyFunctorFactors A n).inv.app L ≫
        (DerivedCategory.homologyFunctor A n).map t) := by
  have ht := (F.mapDerivedCategoryHomologyFunctorIso n).inv.naturality t
  dsimp only [Functor.comp_map] at ht
  rw [Functor.map_comp, Category.assoc, ht]
  simp only [F.map_comp, ← Category.assoc]
  apply congrArg (fun z ↦ z ≫ F.map ((DerivedCategory.homologyFunctor A n).map t))
  rw [← cancel_mono ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app
    (DerivedCategory.Q.obj L))]
  rw [Category.assoc, Iso.inv_hom_id_app,
    F.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  erw [F.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation from neighbourhood sections to exact strict-local sections
sends the sections cohomology class of a cocycle to the restriction of its homology section.
No K-injectivity or localization bijectivity is needed for this assertion.

Source: Stacks Project, Tags 03Q9 and 03QO, the restriction of an injective complex
and commutation of exact inverse image and strict-local sections with homology.
(blueprint: lem-weil-pbc-source-cocycle-exact-restriction).

Proof: evaluate the single-source cocycle degreewise using smallModel_sourceFreeSectionsComplexIso.
Its class in the sections complex is the image of the Hom-complex class under the
homology functor. Apply the natural transformation degreewise. Its naturality with
respect to the cycle inclusion and homology projection identifies the restricted
cycle with the image of the homology section. Exact inverse image and strict-local
global sections preserve kernels and cokernels, hence identify this projection with
the homology projection of the mapped complex. The quotient localization factorization
is natural in the complex map; cancel its inverse with the homology factorization.
The exact-functor homology comparisons are natural in r inverse, so transport along
r gives precisely the displayed composite. Boundaries map to boundaries; thus the
calculation descends to cohomology. Zero cycles and all integer degrees obey the same
calculation. The transformation is arbitrary, so no stalk comparison is used. -/
theorem smallModel_sourceCocycleExactRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (τ : (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1})
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    letI := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let c := CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
    let x := ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      (smallModel_sourceFreeSectionsComplexIso W L).hom)
        ((leftHomologyData
          ((CochainComplex.singleFunctor _ 0).obj
            ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.inv c)
    (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
          G.mapDerivedCategory.map
            (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj))
        x : G.obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
          (U.mapDerivedCategoryPlus.obj K))) =
      (G.map ((U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K))
        (τ.app ((DerivedCategory.Plus.homologyFunctor _ n).obj K)
          (smallModel_sourceCocycleHomologySection K L r n W f hf)) := by
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
  let C := (U.mapHomologicalComplex (.up ℤ)).obj L
  let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
  let b := (DerivedCategory.homologyFunctorFactors _ n).inv.app L ≫
    (DerivedCategory.homologyFunctor _ n).map r.inv
  dsimp only
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  have ha := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.naturality a
  dsimp only [Functor.comp_map] at ha
  erw [← ha]
  simp only [Category.assoc]
  have hg := exactHomologyTransport G C (U.mapDerivedCategory.obj K.obj)
    (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv) n
  erw [hg]
  have hu := exactHomologyTransport U L K.obj r.inv n
  have hu' := congrArg (fun z ↦ z ≫
    (U.mapDerivedCategoryHomologyFunctorIso n).hom.app K.obj) hu
  simp only [Category.assoc, Iso.inv_hom_id_app] at hu'
  dsimp only [Functor.comp_obj] at hu'
  simp only [Category.comp_id] at hu'
  erw [hu']
  rw [G.map_comp, G.map_comp]
  have hp : (U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (U.mapDerivedCategoryHomologyFunctorIso n).hom.app K.obj := by
    simp only [Functor.comp_obj, Functor.mapDerivedCategoryPlusHomologyFunctorIso,
      Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_symm, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
      NatTrans.comp_app, ObjectProperty.ι_obj, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      NatTrans.id_app, Category.comp_id, Category.id_comp]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    exact Category.id_comp _
  rw [hp]
  simp only [← Category.assoc]
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
  have hc := sourceSectionsCocycleRestriction s L n W τ f hf
  dsimp only at hc
  simp only [← Category.assoc] at hc
  erw [hc]
  have ht := τ.naturality b
  dsimp only [Functor.comp_map] at ht
  have hsec : smallModel_sourceCocycleHomologySection K L r n W f hf =
      b.hom.app (op W) (smallModel_sourceFreeSectionsEquiv W _
        (L.liftCycles f (n + 1) (by simp) hf ≫ L.homologyπ n)) := by
    dsimp only [smallModel_sourceCocycleHomologySection, b]
    rw [← smallModel_sourceFreeSectionsEquiv_comp]
    simp only [Category.assoc]
    rfl
  rw [hsec]
  apply congrArg
    ((G.map ((U.mapDerivedCategoryHomologyFunctorIso n).hom.app K.obj)))
  exact (ConcreteCategory.congr_hom ht _).symm
end AlgebraicGeometry.Etale
