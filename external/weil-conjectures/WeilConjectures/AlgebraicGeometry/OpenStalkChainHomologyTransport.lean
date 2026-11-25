/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso
import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkRepresentativeHomology

/-! # Passing an additive open stalk chain square to derived cohomology -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem homology_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
    [(F ⋙ G).PreservesHomology] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  let h := S.leftHomologyData
  let h₁ := (h.map F).map G
  let h₂ := h.map (F ⋙ G)
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G))) h₁ h₂ :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp [h₁, h₂]
      commf' := by simp [h₁, h₂]
      commπ := by simp [h₁, h₂] }
  have hh := γ.homologyMap_eq
  have hh' : h₁.homologyIso.hom = h₂.homologyIso.hom := by
    simpa [γ] using (congrArg (fun k ↦ k ≫ h₂.homologyIso.hom) hh).symm
  rw [h.mapHomologyIso_eq (F ⋙ G), (h.map F).mapHomologyIso_eq G,
    h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  simp only [← G.map_comp, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ k ≫ G.map (F.map h.homologyIso.inv)) hh'.symm

private theorem homology_square
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ C) (E : B ⥤ A) [F.Additive] [E.Additive]
    [F.PreservesHomology] [E.PreservesHomology] [(E ⋙ F).PreservesHomology]
    {S U : ShortComplex A} {T U0 W : ShortComplex B}
    (a : S ⟶ U) (t : S ⟶ T.map E) (b : T ⟶ W) (alpha : U0 ⟶ W)
    (delta : U.map F ⟶ U0.map (E ⋙ F))
    (h : F.mapShortComplex.map a ≫ delta ≫ (E ⋙ F).mapShortComplex.map alpha =
      F.mapShortComplex.map t ≫ (E ⋙ F).mapShortComplex.map b) :
    F.map (ShortComplex.homologyMap t) ≫ F.map (T.mapHomologyIso E).hom ≫
        (E ⋙ F).map (ShortComplex.homologyMap b) =
      F.map (ShortComplex.homologyMap a) ≫ (U.mapHomologyIso F).inv ≫
        ShortComplex.homologyMap delta ≫ (U0.mapHomologyIso (E ⋙ F)).hom ≫
        (E ⋙ F).map (ShortComplex.homologyMap alpha) := by
  have hh := congrArg (fun f ↦ ShortComplex.homologyMap f) h
  simp only [ShortComplex.homologyMap_comp] at hh
  have hcoh := homology_comparison_comp T E F
  apply (cancel_epi (S.mapHomologyIso F).hom).mp
  rw [← reassoc_of% ShortComplex.mapHomologyIso_hom_naturality t F,
    ← reassoc_of% hcoh,
    ← ShortComplex.mapHomologyIso_hom_naturality b (E ⋙ F),
    ← reassoc_of% ShortComplex.mapHomologyIso_hom_naturality a F,
    Iso.hom_inv_id_assoc,
    ← ShortComplex.mapHomologyIso_hom_naturality alpha (E ⋙ F)]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ (W.mapHomologyIso (E ⋙ F)).hom) hh.symm

/-- An additive chain square induces the corresponding open derived stalk square.

Proof: assemble the degreewise equality as an equality of additive complex maps
and apply homologyMap. Its composition law and naturality of mapHomologyIso move
homology past the forgetful functors. Restriction of scalars followed by forgetting
is the same additive functor as forgetting over the new ring; the canonical
homology comparisons agree, as follows from their universal kernel and cokernel
identities. Expand openDerivedStalkIso and openRestrictionRepresentativeIso.
Their derived restriction comparison factors cancel. The remaining exact-stalk
and exact-restriction homology factors are the homology comparison of the inverse
same-germ stalk map, by naturality of exact-functor homology. Finally apply
comparisonStalkHomologyIso_naturality to alpha and cancel the invertible homology
comparisons at each endpoint. This yields exactly the displayed equality.
No tensor complex or normalized input coordinate is involved. No injectivity,
surjectivity or nonzero condition on the complexes or their homology is used.
Source: Stacks Project, Tags 0098 and 0D5U; Mathlib exact-functor homology
naturality and the localization factorization of exact functors.
(blueprint: lem-pc-open-stalk-chain-homology-transport). -/
theorem openStalk_chain_homology_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (y : Y) (i : ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (N0 : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (V : CochainComplex (ModuleCat.{u} (Z.presheaf.stalk (j y))) ℤ)
    (V0 : CochainComplex (ModuleCat.{u} (Y.presheaf.stalk y)) ℤ)
    (e : Z.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y)
    (t : V ⟶ ((ModuleCat.restrictScalars.{u} e.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj V0)
    (a : V ⟶ ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
      (.up ℤ)).obj N)
    (b : V0 ⟶ ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
      (.up ℤ)).obj N0)
    (alpha : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N ⟶ N0)
    (h : ∀ k : ℤ,
      (forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}).map (a.f k) ≫
        (Scheme.Modules.restrictStalkNatIso j y).inv.app (N.X k) ≫
        (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}).map
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map (alpha.f k)) =
      (forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}).map (t.f k) ≫
        (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}).map (b.f k)) :
    let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
    let HU := comparisonStalkCohomology Y y i ⋙ F0
    F.map (HomologicalComplex.homologyMap t i) ≫
        F.map ((V0.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} e.toRingHom)).hom ≫
        F0.map (HomologicalComplex.homologyMap b i ≫
          (comparisonStalkHomologyIso Y y N0 i).inv) =
      F.map (HomologicalComplex.homologyMap a i ≫
        (comparisonStalkHomologyIso Z (j y) N i).inv) ≫
        (openDerivedStalkIso j y i).hom.app (DerivedCategory.Q.obj N) ≫
        HU.map ((openRestrictionRepresentativeIso j N).inv ≫ DerivedCategory.Q.map alpha)
    := by
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let S := (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
    (.up ℤ)
  let S0 := (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
    (.up ℤ)
  let R := (Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)
  let E := ModuleCat.restrictScalars.{u} e.toRingHom
  let HU := comparisonStalkCohomology Y y i ⋙ F0
  let δ := (N.sc i).mapNatTrans
    (show (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y) ⋙ F) ⟶
      (openRestrictionFunctor j ⋙
        RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙ F0) from
      (Scheme.Modules.restrictStalkNatIso j y).inv)
  let ca := (HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map a
  let ct := (HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map t
  let cb := (HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map b
  let cα := (HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (S0.map alpha)
  have hs : F.mapShortComplex.map ca ≫ δ ≫ F0.mapShortComplex.map cα =
      F.mapShortComplex.map ct ≫ F0.mapShortComplex.map cb := by
    ext1
    · exact h _
    · exact h _
    · exact h _
  have hα : F0.map (comparisonStalkHomologyIso Y y (R.obj N) i).inv ≫
      HU.map (DerivedCategory.Q.map alpha) =
      F0.map (HomologicalComplex.homologyMap (S0.map alpha) i) ≫
        F0.map (comparisonStalkHomologyIso Y y N0 i).inv := by
    have hn := comparisonStalkHomologyIso_naturality Y y alpha i
    have hi : (comparisonStalkHomologyIso Y y (R.obj N) i).inv ≫
        (comparisonStalkCohomology Y y i).map (DerivedCategory.Q.map alpha) =
        HomologicalComplex.homologyMap (S0.map alpha) i ≫
          (comparisonStalkHomologyIso Y y N0 i).inv := by
      apply (cancel_epi (comparisonStalkHomologyIso Y y (R.obj N) i).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using congrArg
        (fun k ↦ k ≫ (comparisonStalkHomologyIso Y y N0 i).inv) hn
    simpa only [HU, Functor.comp_map, Functor.map_comp] using
      congrArg (fun k ↦ F0.map k) hi
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% openDerivedStalk_representative_homology j y i N]
  erw [hα]
  have hp := homology_square F E (T := V0.sc i)
    (U0 := (S0.obj (R.obj N)).sc i) (W := (S0.obj N0).sc i) ca ct cb cα δ hs
  exact congrArg
    (fun k ↦ k ≫ F0.map (comparisonStalkHomologyIso Y y N0 i).inv) hp

end AlgebraicGeometry.SingleComplexBaseChange
