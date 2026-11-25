/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison

/-! # Naturality of the source derived-sections comparison

Source: Stacks Project, Tags 03Q8 and 03Q9. We check precomposition on cochains,
cocycles, their quotient, and the corresponding derived morphisms.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the localization and derived Hom part of the source comparison.
Source: Stacks Project, Tags 03Q8 and 03Q9.
(blueprint: lem-weil-pbc-source-derived-sections-naturality-core)

The proof is the cocycle computation: precomposition on the Hom complex descends
through cocycles and boundaries, and the quotient and the specified derived
representative preserve this map. -/
theorem sourceDerivedSections_naturality_core
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let e₀ := fun W : C ↦
      sourcePlusHomIso ((strictLocalFreeSheaf T).obj W) K L q n
    AddCommGrpCat.ofHom (Preadditive.leftComp (K⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e₀ U).hom =
      (e₀ V).hom ≫ AddCommGrpCat.ofHom (Preadditive.leftComp ((DerivedCategory.Q.obj L)⟦n⟧)
        ((DerivedCategory.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) := by
  ext x
  dsimp [sourcePlusHomIso, AddEquiv.mk', Iso.homCongr,
    Functor.FullyFaithful.homEquiv, Preadditive.leftComp]
  simp only [Category.id_comp, Category.assoc]
  rfl

section HomPrecomposition

/-- Precomposition on the Hom complex, commuting with its differential. -/
private def sourceHomPrecomp
    {D : Type (v + 2)} [Category.{v + 1} D] [Preadditive D]
    {F G : CochainComplex D ℤ} (f : F ⟶ G) (L : CochainComplex D ℤ) :
    HomComplex G L ⟶ HomComplex F L where
  f n := AddCommGrpCat.ofHom
    { toFun z := (Cochain.ofHom f).comp z (zero_add n)
      map_zero' := by simp
      map_add' z z' := by simp [Cochain.comp_add] }
  comm' i j hij := by
    ext z
    exact δ_ofHom_comp f z j

/-- Precomposition restricts to the additive group of cocycles. -/
private def sourceCocyclePrecomp
    {D : Type (v + 2)} [Category.{v + 1} D] [Preadditive D]
    {F G : CochainComplex D ℤ} (f : F ⟶ G) (L : CochainComplex D ℤ) (n : ℤ) :
    Cocycle G L n →+ Cocycle F L n where
  toFun z := z.precomp f
  map_zero' := by ext; simp [Cocycle.precomp]
  map_add' z z' := by ext; simp [Cocycle.precomp, Cochain.comp_add]

/-- Precomposition descends to classes since it carries boundaries to boundaries. -/
private def sourceClassPrecomp
    {D : Type (v + 2)} [Category.{v + 1} D] [Preadditive D]
    {F G : CochainComplex D ℤ} (f : F ⟶ G) (L : CochainComplex D ℤ) (n : ℤ) :
    CohomologyClass G L n →+ CohomologyClass F L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom F L n).comp (sourceCocyclePrecomp f L n)) (by
      rintro z ⟨m, hm, β, hβ⟩
      change CohomologyClass.mk (z.precomp f) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, (Cochain.ofHom f).comp β (zero_add m), ?_⟩
      rw [δ_ofHom_comp, hβ]
      rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit quotient map agrees with the induced map on homology. -/
private theorem sourceClassPrecomp_homology
    {D : Type (v + 2)} [Category.{v + 1} D] [Preadditive D]
    {F G : CochainComplex D ℤ} (f : F ⟶ G) (L : CochainComplex D ℤ) (n : ℤ) :
    (leftHomologyData G L n).homologyIso.inv ≫
        HomologicalComplex.homologyMap (sourceHomPrecomp f L) n =
      AddCommGrpCat.ofHom (sourceClassPrecomp f L n) ≫
        (leftHomologyData F L n).homologyIso.inv := by
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (sourceHomPrecomp f L)) (leftHomologyData G L n) (leftHomologyData F L n) :=
    { φK := AddCommGrpCat.ofHom (sourceCocyclePrecomp f L n)
      φH := AddCommGrpCat.ofHom (sourceClassPrecomp f L n)
      commi := by ext z; rfl
      commf' := by
        ext z : 2
        apply Subtype.ext
        exact (δ_ofHom_comp f z n).symm
      commπ := by ext z; rfl }
  rw [show HomologicalComplex.homologyMap (sourceHomPrecomp f L) n =
    ShortComplex.homologyMap _ from rfl, γ.homologyMap_eq]
  simp
  rfl

end HomPrecomposition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Localization of a precomposed cocycle is precomposition of its derived morphism. -/
private theorem sourceClassDerivedHomIso_precomp_mk
    {C : Type (v + 2)} [Category.{v + 1} C] [Abelian C] [HasDerivedCategory.{v + 1} C]
    {A B : C} (f : A ⟶ B) (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ)
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj B) L n) :
    (sourceClassDerivedHomIso A L n).hom
        (CohomologyClass.mk (z.precomp ((CochainComplex.singleFunctor C 0).map f))) =
      (DerivedCategory.singleFunctor C 0).map f ≫
        (sourceClassDerivedHomIso B L n).hom (CohomologyClass.mk z) := by
  dsimp [sourceClassDerivedHomIso, AddEquiv.mk', Iso.homCongr]
  dsimp [Functor.mapAddHom, CohomologyClass.homAddEquiv, AddEquiv.ofBijective]
  erw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp]
  simp only [Functor.map_comp, Category.assoc]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  erw [← NatTrans.naturality_assoc]

/-- The cocycle calculation descends to the square on all cohomology classes. -/
@[reassoc]
private theorem sourceClassDerivedHomIso_precomp
    {C : Type (v + 2)} [Category.{v + 1} C] [Abelian C] [HasDerivedCategory.{v + 1} C]
    {A B : C} (f : A ⟶ B) (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    AddCommGrpCat.ofHom (sourceClassPrecomp ((CochainComplex.singleFunctor C 0).map f) L n) ≫
        (sourceClassDerivedHomIso A L n).hom =
      (sourceClassDerivedHomIso B L n).hom ≫ AddCommGrpCat.ofHom
        (Preadditive.leftComp ((DerivedCategory.Q.obj L)⟦n⟧)
          ((DerivedCategory.singleFunctor C 0).map f)) := by
  ext x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  exact sourceClassDerivedHomIso_precomp_mk f L n z

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Free-generator evaluation commutes degreewise with restriction of sections. -/
private theorem sourceFreeSectionsComplexIso_naturality
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ)
    {U V : C} (a : U ⟶ V) :
    sourceHomPrecomp ((CochainComplex.singleFunctor _ 0).map
        ((strictLocalFreeSheaf T).map a)) L ≫ (sourceFreeSectionsComplexIso U L).hom =
      (sourceFreeSectionsComplexIso V L).hom ≫
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  ext n z
  obtain ⟨z, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  dsimp [sourceHomPrecomp, sourceFreeSectionsComplexIso]
  rw [← Cochain.fromSingleMk_precomp]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  change (strictLocalFreeSheafSections (L.X n)).app (op U)
      ((strictLocalFreeSheaf T).map a ≫ z) =
    (L.X n).obj.map a.op ((strictLocalFreeSheafSections (L.X n)).app (op V) z)
  exact congrArg (fun k ↦ k z) ((strictLocalFreeSheafSections (L.X n)).naturality a.op)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Naturality of evaluation of the Hom complex at the free sheaf generator.
Source: Stacks Project, Tags 03Q8 and 03Q9.
(blueprint: lem-weil-pbc-source-derived-sections-naturality-evaluation)

This is the degreewise Yoneda calculation: the free-sheaf evaluation sends
precomposition by the map induced by `a` to restriction of sections, and the
left-homology comparison is functorial. -/
theorem sourceDerivedSections_naturality_evaluation
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
    let e₁ := fun W : C ↦
      (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj W) L n).symm ≪≫
      (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf T).obj W)) L n).homologyIso.symm ≪≫
      H.mapIso (sourceFreeSectionsComplexIso W L)
    AddCommGrpCat.ofHom (Preadditive.leftComp ((DerivedCategory.Q.obj L)⟦n⟧)
      ((DerivedCategory.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e₁ U).hom =
      (e₁ V).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  clear q K
  dsimp only
  rw [← cancel_epi (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj V) L n).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← sourceClassDerivedHomIso_precomp_assoc]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc,
    ← sourceClassPrecomp_homology ((CochainComplex.singleFunctor _ 0).map
      ((strictLocalFreeSheaf T).map a)) L n]
  simp only [Category.assoc]
  simp only [Functor.mapIso_hom]
  change _ ≫ (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map
    (sourceHomPrecomp ((CochainComplex.singleFunctor _ 0).map
      ((strictLocalFreeSheaf T).map a)) L) ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map
      (sourceFreeSectionsComplexIso U L).hom = _
  rw [← Functor.map_comp, sourceFreeSectionsComplexIso_naturality, Functor.map_comp]

/-- Composition of the localization and evaluation squares gives the displayed
source comparison square. This is the categorical pasting step in Tags 03Q8--03Q9.
(blueprint: lem-weil-pbc-source-derived-sections-naturality-compose) -/
theorem sourceDerivedSections_naturality_compose
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
    let e₀ := fun W : C ↦ sourcePlusHomIso ((strictLocalFreeSheaf T).obj W) K L q n
    let e₁ := fun W : C ↦
      (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj W) L n).symm ≪≫
      (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf T).obj W)) L n).homologyIso.symm ≪≫
      H.mapIso (sourceFreeSectionsComplexIso W L)
    AddCommGrpCat.ofHom (Preadditive.leftComp (K⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e₀ U).hom ≫ (e₁ U).hom =
      (e₀ V).hom ≫ (e₁ V).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  dsimp only
  rw [← Category.assoc,
    sourceDerivedSections_naturality_core K L q n a]
  rw [Category.assoc, sourceDerivedSections_naturality_evaluation K L q n a]

end AlgebraicGeometry.Etale
