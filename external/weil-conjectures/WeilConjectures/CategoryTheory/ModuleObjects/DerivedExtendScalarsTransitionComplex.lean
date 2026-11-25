/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransition

/-!
# The transition between reductions on complexes

Let `φ' : R ⟶ S'`, `ψ : S' ⟶ S` and `φ : R ⟶ S` be morphisms of commutative algebra objects with
`φ' ≫ ψ = φ`. On the image of a complex `P`, the transition `t : S' ⊗ᴸ_R P ⟶ S ⊗ᴸ_R P` of
`Mod.derivedReductionTransition` is computed by the levelwise map `S' ⊗_R P ⟶ S ⊗_R P`
(`Mod.derivedReductionTransition_app_Q_obj_comp`). As a consequence, if
`0 ⟶ R --k'--> R --φ'--> S' ⟶ 0` and `0 ⟶ R --k--> R --φ--> S ⟶ 0` are short exact with
`k' = m * k`, the connecting morphisms of the natural reduction triangles satisfy `t ≫ δ = δ' ≫ m`
(`Mod.derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ`): on a complex of flat
modules, `(m, 1, S' ⊗ P ⟶ S ⊗ P)` is a map of short exact sequences from
`P --k'--> P ⟶ S' ⊗ P` to `P --k--> P ⟶ S ⊗ P`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S' S : C} [MonObj R] [MonObj S'] [MonObj S] [IsCommMonObj R] [IsCommMonObj S']
  [IsCommMonObj S] (φ' : R ⟶ S') [IsMonHom φ'] (ψ : S' ⟶ S) [IsMonHom ψ] (φ : R ⟶ S)
  [IsMonHom φ] (h : φ' ≫ ψ = φ)

/-! ### The levelwise transition -/

/-- The levelwise transition `S' ⊗_R M ⟶ S ⊗_R M`, as a map of `S'`-modules: the unit of
extension of scalars along `ψ`, followed by the transitivity isomorphism. -/
noncomputable def extendScalarsTransition : extendScalars φ' ⟶ extendScalars φ ⋙ comap ψ :=
  Functor.whiskerLeft (extendScalars φ') (extendRestrictAdjunction ψ).unit ≫
    Functor.whiskerRight ((extendScalarsComp φ' ψ).symm ≪≫ extendScalarsIsoOfEq h).hom (comap ψ)

/-- The levelwise transition `S' ⊗_R M ⟶ S ⊗_R M`, as a map of `R`-modules. -/
noncomputable def extendComapTransition :
    extendScalars φ' ⋙ comap φ' ⟶ extendScalars φ ⋙ comap φ :=
  Functor.whiskerRight (extendScalarsTransition φ' ψ φ h) (comap φ') ≫
    Functor.whiskerLeft (extendScalars φ) ((comapComp φ' ψ).symm ≪≫ comapCongr h).hom

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
/-- The levelwise transition is compatible with the units: `M ⟶ S' ⊗_R M ⟶ S ⊗_R M` is the unit
`M ⟶ S ⊗_R M`. -/
@[reassoc]
lemma extendRestrictAdjunction_unit_app_comp_extendComapTransition_app (M : Mod C R) :
    (extendRestrictAdjunction φ').unit.app M ≫ (extendComapTransition φ' ψ φ h).app M =
      (extendRestrictAdjunction φ).unit.app M := by
  have n := ((comapComp φ' ψ).symm ≪≫ comapCongr h).hom.naturality
    (((extendScalarsComp φ' ψ).symm ≪≫ extendScalarsIsoOfEq h).hom.app M)
  have u := extendRestrictAdjunction_unit_app_comp_map_extendScalarsComp φ' ψ φ h M
  simp only [Functor.comp_map] at n
  simp only [extendComapTransition, extendScalarsTransition, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [n]
  erw [← reassoc_of% u]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]

/-- The levelwise transition `S' ⊗_R P ⟶ S ⊗_R P` on complexes. -/
noncomputable abbrev extendComapComplexTransition :
    extendComapComplexFunctor φ' ⟶ extendComapComplexFunctor φ :=
  NatTrans.mapHomologicalComplex (extendComapTransition φ' ψ φ h) (ComplexShape.up ℤ)

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
/-- The levelwise transition on complexes is compatible with the units. -/
@[reassoc]
lemma extendUnitComplexHom_comp_extendComapComplexTransition_app
    (P : CochainComplex (Mod C R) ℤ) :
    extendUnitComplexHom φ' P ≫ (extendComapComplexTransition φ' ψ φ h).app P =
      extendUnitComplexHom φ P := by
  ext i : 1
  simp only [HomologicalComplex.comp_f, extendUnitComplexHom_f,
    NatTrans.mapHomologicalComplex_app_f]
  rw [← extendRestrictAdjunction_unit_app, ← extendRestrictAdjunction_unit_app]
  exact extendRestrictAdjunction_unit_app_comp_extendComapTransition_app φ' ψ φ h (P.X i)

/-! ### The transition on complexes -/

/-- Two morphisms `f g : G (F X) ⟶ W` which, followed by a monomorphism `e : W ⟶ G Y`, become
images `G.map uf`, `G.map ug`, are equal as soon as they agree after precomposition with the
unit of `F ⊣ G`. -/
lemma _root_.CategoryTheory.Adjunction.eq_of_comp_eq_map {𝒜 ℬ : Type*} [Category* 𝒜]
    [Category* ℬ] {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜} (adj : F ⊣ G) {X W : 𝒜} {Y : ℬ}
    {f g : G.obj (F.obj X) ⟶ W} (e : W ⟶ G.obj Y) [Mono e] (uf ug : F.obj X ⟶ Y)
    (hf : f ≫ e = G.map uf) (hg : g ≫ e = G.map ug)
    (h : adj.unit.app X ≫ f = adj.unit.app X ≫ g) : f = g := by
  obtain rfl : uf = ug := (adj.homEquiv X Y).injective (by
    rw [adj.homEquiv_unit, adj.homEquiv_unit, ← hf, ← hg, reassoc_of% h])
  rw [← cancel_mono e, hf, hg]

/-- **The transition on a complex** `P` is the levelwise map `S' ⊗_R P ⟶ S ⊗_R P`, read
through the comparisons `Mod.derivedExtendComapComparison`. -/
lemma derivedReductionTransition_app_Q_obj_comp (P : CochainComplex (Mod C R) ℤ) :
    (derivedReductionTransition φ' ψ φ h).app (DerivedCategory.Q.obj P) ≫
        derivedExtendComapComparison φ P =
      derivedExtendComapComparison φ' P ≫
        DerivedCategory.Q.map ((extendComapComplexTransition φ' ψ φ h).app P) := by
  let Y₀ := ((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
    ((HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj P)
  let e : DerivedCategory.Q.obj ((extendComapComplexFunctor φ).obj P) ⟶
      (comap φ').mapDerivedCategory.obj ((comap ψ).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj Y₀)) :=
    (DerivedCategory.quotientCompQhIso (Mod C R)).inv.app _ ≫
      (comap φ).mapDerivedCategoryFactorsh.inv.app Y₀ ≫
      (mapDerivedCategoryComapCompIso φ' ψ φ h).inv.app _
  have : Mono e := mono_comp' inferInstance (mono_comp'
    (by exact (inferInstance : Mono ((comap φ).mapDerivedCategoryFactorsh.inv.app Y₀)))
    inferInstance)
  -- the comparison `T (Qh P) ⟶ Qh (S ⊗_R P)`, read back through `D(Res_φ)`
  have Hh : derivedExtendComapComparisonh φ P ≫ (comap φ).mapDerivedCategoryFactorsh.inv.app Y₀ =
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj P)) :=
    (Category.assoc _ _ _).trans (by erw [Iso.hom_inv_id_app, Category.comp_id])
  have H : derivedExtendComapComparison φ P ≫ e =
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P) ≫
        (extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P)) ≫
        (mapDerivedCategoryComapCompIso φ' ψ φ h).inv.app (DerivedCategory.Qh.obj Y₀) := by
    dsimp only [derivedExtendComapComparison, e]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [Functor.map_comp, Category.assoc]
    exact _ ≫= ((Category.assoc _ _ _).symm.trans (Hh =≫ _))
  refine (derivedExtendMapDerivedCategoryAdjunction φ').eq_of_comp_eq_map e
    ((derivedExtendScalarsTransition φ' ψ φ h).app (DerivedCategory.Q.obj P) ≫
      (comap ψ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P) ≫
        (extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P)))
    ((extendScalars φ').leftDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P) ≫
      (extendScalars φ').leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj P) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (extendScalarsTransition φ' ψ φ h)
          (ComplexShape.up ℤ)).app P)) ≫
      (comap ψ).mapDerivedCategoryFactorsh.inv.app Y₀) ?_ ?_ ?_
  · have n := (mapDerivedCategoryComapCompIso φ' ψ φ h).inv.naturality
      ((extendScalars φ).leftDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P) ≫
        (extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P))
    simp only [Functor.comp_map] at n
    rw [Category.assoc, H, derivedReductionTransition, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
    erw [n]
    rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
  · have hT : (extendComapComplexTransition φ' ψ φ h).app P =
        ((comap φ').mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex
          (extendScalarsTransition φ' ψ φ h) (ComplexShape.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex ((comapComp φ' ψ).symm ≪≫ comapCongr h).hom
          (ComplexShape.up ℤ)).app (((extendScalars φ).mapHomologicalComplex _).obj P) := by
      ext n : 1
      rfl
    have L := mapDerivedCategoryComapCompIso_hom_app_Qh_obj_comp_factorsh φ' ψ φ h Y₀
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at L
    erw [Category.id_comp] at L
    rw [NatTrans.mapHomotopyCategory_app] at L
    have hc : (comap φ').mapDerivedCategoryFactorsh.hom.app
          (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y₀) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex ((comapComp φ' ψ).symm ≪≫ comapCongr h).hom
            (ComplexShape.up ℤ)).app (((extendScalars φ).mapHomologicalComplex _).obj P))) ≫
        (comap φ).mapDerivedCategoryFactorsh.inv.app Y₀ ≫
        (mapDerivedCategoryComapCompIso φ' ψ φ h).inv.app (DerivedCategory.Qh.obj Y₀) =
        (comap φ').mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.inv.app Y₀) := by
      rw [← cancel_epi ((comap φ').mapDerivedCategory.map
        ((comap ψ).mapDerivedCategoryFactorsh.hom.app Y₀)), ← Functor.map_comp,
        Iso.hom_inv_id_app, Functor.map_id]
      erw [← reassoc_of% L]
      exact (_ ≫= ((Category.assoc _ _ _).symm.trans
        (((comap φ).mapDerivedCategoryFactorsh.hom_inv_id_app Y₀ =≫ _).trans
          (Category.id_comp _)))).trans
        ((mapDerivedCategoryComapCompIso φ' ψ φ h).hom_inv_id_app _)
    have nf : (comap φ').mapDerivedCategoryFactorsh.hom.app
          (((extendScalars φ').mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (((comap φ').mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex
            (extendScalarsTransition φ' ψ φ h) (ComplexShape.up ℤ)).app P))) =
        (comap φ').mapDerivedCategory.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
            (extendScalarsTransition φ' ψ φ h) (ComplexShape.up ℤ)).app P))) ≫
        (comap φ').mapDerivedCategoryFactorsh.hom.app
          (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y₀) :=
      ((comap φ').mapDerivedCategoryFactorsh.hom.naturality
        ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
          (extendScalarsTransition φ' ψ φ h) (ComplexShape.up ℤ)).app P))).symm
    have K : (comap φ').mapDerivedCategoryFactorsh.hom.app
          (((extendScalars φ').mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((extendComapComplexTransition φ' ψ φ h).app P)) ≫
        (comap φ).mapDerivedCategoryFactorsh.inv.app Y₀ ≫
        (mapDerivedCategoryComapCompIso φ' ψ φ h).inv.app (DerivedCategory.Qh.obj Y₀) =
        (comap φ').mapDerivedCategory.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
            (extendScalarsTransition φ' ψ φ h) (ComplexShape.up ℤ)).app P))) ≫
        (comap φ').mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.inv.app Y₀) := by
      rw [hT]
      exact (_ ≫= ((((congrArg DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map_comp _ _)).trans
          (DerivedCategory.Qh.map_comp _ _)) =≫ _).trans (Category.assoc _ _ _))).trans
        ((Category.assoc _ _ _).symm.trans ((nf =≫ _).trans
          ((Category.assoc _ _ _).trans (_ ≫= hc))))
    have K' : derivedExtendComapComparisonh φ' P ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((extendComapComplexTransition φ' ψ φ h).app P)) ≫
        (comap φ).mapDerivedCategoryFactorsh.inv.app Y₀ ≫
        (mapDerivedCategoryComapCompIso φ' ψ φ h).inv.app (DerivedCategory.Qh.obj Y₀) =
        (comap φ').mapDerivedCategory.map ((extendScalars φ').leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P)) ≫
        (comap φ').mapDerivedCategory.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
            (extendScalarsTransition φ' ψ φ h) (ComplexShape.up ℤ)).app P))) ≫
        (comap φ').mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.inv.app Y₀) :=
      (Category.assoc _ _ _).trans (_ ≫= K)
    dsimp only [derivedExtendComapComparison, e]
    simp only [Category.assoc]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc, Iso.hom_inv_id_app_assoc, K']
    exact ((Functor.map_comp _ _ _).trans (_ ≫= ((Functor.map_comp _ _ _).trans
      (_ ≫= (Functor.map_comp _ _ _))))).symm
  · rw [← Category.assoc, unit_app_comp_derivedReductionTransition_app,
      unit_app_comp_derivedExtendComapComparison,
      unit_app_comp_derivedExtendComapComparison_assoc, ← Functor.map_comp,
      extendUnitComplexHom_comp_extendComapComplexTransition_app]

variable {φ' φ} (k' k m : ℤ) (hk : k' = m * k) (w' : (k' • 𝟙 R) ≫ φ' = 0)
  (hφ' : (ShortComplex.mk _ _ w').ShortExact) (w : (k • 𝟙 R) ≫ φ = 0)
  (hφ : (ShortComplex.mk _ _ w).ShortExact)

include hk in
/-- The compatibility `t ≫ δ = δ' ≫ m` on a complex of flat modules: there, `δ` and `δ'`
are the connecting morphisms of the short exact reduction sequences, and `(m, 1, t)` is a map of
short exact sequences. -/
lemma derivedReductionTransition_app_Q_obj_comp_derivedExtendScalarsTriangleδ
    (P : CochainComplex (Mod C R) ℤ) (hflat : ∀ n, ObjectProperty.flat (P.X n)) :
    (derivedReductionTransition φ' ψ φ h).app (DerivedCategory.Q.obj P) ≫
        (derivedExtendScalarsTriangleδ k w hφ).app (DerivedCategory.Q.obj P) =
      (derivedExtendScalarsTriangleδ k' w' hφ').app (DerivedCategory.Q.obj P) ≫
        (m • 𝟙 (DerivedCategory.Q.obj P))⟦(1 : ℤ)⟧' := by
  have hS := shortExact_extendUnitComplexHom k w hφ P hflat
  have hS' := shortExact_extendUnitComplexHom k' w' hφ' P hflat
  let f : reductionShortComplex k' w' P ⟶ reductionShortComplex k w P :=
    { τ₁ := m • 𝟙 P
      τ₂ := 𝟙 P
      τ₃ := (extendComapComplexTransition φ' ψ φ h).app P
      comm₁₂ := by
        dsimp only [reductionShortComplex]
        rw [hk, Category.comp_id, Preadditive.zsmul_comp, Category.id_comp, mul_smul]
      comm₂₃ := by
        rw [Category.id_comp]
        exact (extendUnitComplexHom_comp_extendComapComplexTransition_app φ' ψ φ h P).symm }
  have hn := DerivedCategory.triangleOfSESδ_naturality hS' hS f
  rw [derivedExtendScalarsTriangleδ_app_Q_obj_of_shortExact k w hφ P hS,
    derivedExtendScalarsTriangleδ_app_Q_obj_of_shortExact k' w' hφ' P hS', ← Category.assoc,
    derivedReductionTransition_app_Q_obj_comp φ' ψ φ h P, Category.assoc, Category.assoc]
  erw [← hn]
  rw [Functor.map_zsmul, Functor.map_id]

include hk in
/-- **The transition and the connecting morphisms of the reduction triangles**: if
`0 ⟶ R --k'--> R --φ'--> S' ⟶ 0` and `0 ⟶ R --k--> R --φ--> S ⟶ 0` are short exact and
`k' = m * k`, then `t ≫ δ = δ' ≫ m`, where `δ` and `δ'` are the connecting morphisms of the
natural reduction triangles (`Mod.derivedExtendScalarsTriangleδ`). -/
lemma derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ
    (K : DerivedCategory (Mod C R)) :
    (derivedReductionTransition φ' ψ φ h).app K ≫ (derivedExtendScalarsTriangleδ k w hφ).app K =
      (derivedExtendScalarsTriangleδ k' w' hφ').app K ≫ (m • 𝟙 K)⟦(1 : ℤ)⟧' := by
  let L := DerivedCategory.Q.objPreimage K
  let g : DerivedCategory.Q.obj ((CochainComplex.flatResolutionFunctor _).obj L) ⟶ K :=
    DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app L) ≫
      (DerivedCategory.Q.objObjPreimageIso K).hom
  have : IsIso g := by
    dsimp only [g]
    infer_instance
  have h₁ := (derivedReductionTransition φ' ψ φ h).naturality g
  have h₂ := (derivedExtendScalarsTriangleδ k w hφ).naturality g
  have h₃ := (derivedExtendScalarsTriangleδ k' w' hφ').naturality g
  have key := derivedReductionTransition_app_Q_obj_comp_derivedExtendScalarsTriangleδ ψ h k' k m
    hk w' hφ' w hφ _ (CochainComplex.flat_flatResolutionFunctor_obj_X L)
  rw [← cancel_epi
    (((extendScalars φ').leftDerivedFunctor ⋙ (comap φ').mapDerivedCategory).map g),
    ← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, key,
    ← Category.assoc
      (((extendScalars φ').leftDerivedFunctor ⋙ (comap φ').mapDerivedCategory).map g),
    h₃]
  simp only [Category.assoc, ← Functor.map_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.id_comp, Category.comp_id]

end CategoryTheory.Mod
