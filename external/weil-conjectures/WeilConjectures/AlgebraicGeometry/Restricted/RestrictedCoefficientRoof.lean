/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionRoofModels
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.Restricted.RestrictedCoefficientNatRoof
import WeilConjectures.CategoryTheory.MapExtendHomology

/-! # Restricted coefficient maps on the cohomology of an injective roof

## References

* Stacks Project, Cohomology, Tags 01E4 and 01FB
* Stacks Project, Tag 01FB (Remark explain-arrow), Tag 01E4 (restriction of an injective resolution)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w vD uD vE uE vB uB
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor
  ComplexShape.embeddingUpNat

private theorem inverse_naturality {C : Type*} [Category C] {A B D E : C}
    (eK : A ≅ B) (eL : D ≅ E) (f : B ⟶ E) (g : A ⟶ D)
    (h : g ≫ eL.hom = eK.hom ≫ f) : f ≫ eL.inv = eK.inv ≫ g := by
  apply (cancel_epi eK.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem map_eqToHom_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {Z : D} (p : X = Y) (q : F.obj Y = Z)
    (r : F.obj X = Z) : eqToHom r = F.map (eqToHom p) ≫ eqToHom q := by
  simp only [eqToHom_map, eqToHom_trans]

private theorem paste_equalities {C : Type*} [Category C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ E} {d : E ⟶ D}
    {e : D ⟶ F} {f : E ⟶ G} {g : G ⟶ F}
    (h1 : a ≫ b = c ≫ d) (h2 : d ≫ e = f ≫ g) :
    (c ≫ f) ≫ g = a ≫ (b ≫ e) := by
  simp only [Category.assoc]
  rw [← h2, ← Category.assoc, ← h1, Category.assoc]

private theorem map_relation {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B E : C} {T : D} (a : T ⟶ H.obj A)
    (f : A ⟶ B) (g : B ⟶ E) (h : A ⟶ E) (heq : f ≫ g = h) :
    (a ≫ H.map f) ≫ H.map g = a ≫ H.map h := by
  rw [Category.assoc, ← H.map_comp, heq]

private def sectionExtendIso
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (q : ℕ) :=
  (CochainComplex.mapExtendHomologyIso E K q).symm

private theorem sectionExtendIso_naturality
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] {K L : CochainComplex D ℕ} (φ : K ⟶ L) (q : ℕ) :
    (sectionExtendIso E K q).hom ≫ HomologicalComplex.homologyMap
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) (q : ℤ) =
      HomologicalComplex.homologyMap
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) q ≫
          (sectionExtendIso E L q).hom := by
  let e := ComplexShape.embeddingUpNat
  let EK := ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso e
    (rfl : (q : ℤ) = q)
  let EL := ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso e
    (rfl : (q : ℤ) = q)
  have he : HomologicalComplex.homologyMap
      ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) q ≫ EL.inv =
      EK.inv ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) e) (q : ℤ) := by
    exact inverse_naturality EK EL
      (HomologicalComplex.homologyMap
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) q)
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) e) (q : ℤ))
      (HomologicalComplex.extendHomologyIso_hom_naturality
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) e rfl)
  have hm := congrArg
    (fun z ↦ HomologicalComplex.homologyMap z (q : ℤ))
    ((e.mapExtendFunctorNatIso E).inv.naturality φ)
  simp only [HomologicalComplex.homologyMap_comp] at hm
  change HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) e) (q : ℤ) ≫
      HomologicalComplex.homologyMap (L.mapExtendIso e E).inv (q : ℤ) =
    HomologicalComplex.homologyMap (K.mapExtendIso e E).inv (q : ℤ) ≫
      HomologicalComplex.homologyMap
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ e)) (q : ℤ) at hm
  unfold sectionExtendIso CochainComplex.mapExtendHomologyIso
  dsimp only [Iso.symm, Iso.trans, Functor.mapIso]
  exact paste_equalities he hm

private theorem mapExtendIso_comp_hom
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (F : D ⥤ E) (G : E ⥤ B) [F.Additive] [G.Additive] (K : CochainComplex D ℕ) :
    (K.mapExtendIso ComplexShape.embeddingUpNat (F ⋙ G)).hom =
      (G.mapHomologicalComplex _).map
        (K.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
      (((F.mapHomologicalComplex _).obj K).mapExtendIso
        ComplexShape.embeddingUpNat G).hom := by
  ext i
  by_cases hi : ∃ j, ComplexShape.embeddingUpNat.f j = i
  · obtain ⟨j, rfl⟩ := hi
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    dsimp [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
    rw [HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f j),
      HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f j),
      HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f j)]
    apply map_eqToHom_comp G
    all_goals
      simp only [HomologicalComplex.extend, ComplexShape.Embedding.r_f,
        HomologicalComplex.extend.X]
      rfl
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ _ _ (by simpa using hi)

private theorem sectionExtendIso_comp
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (F : D ⥤ E) (G : E ⥤ B) [F.Additive] [hG : G.Additive]
    (K : CochainComplex D ℕ) (q : ℕ) :
    (sectionExtendIso (F ⋙ G) K q).hom ≫ HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (K.mapExtendIso ComplexShape.embeddingUpNat F).hom) (q : ℤ) =
      (sectionExtendIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) q).hom := by
  let mF := K.mapExtendIso ComplexShape.embeddingUpNat F
  let mG := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).mapExtendIso
    ComplexShape.embeddingUpNat G
  let mFG := K.mapExtendIso ComplexShape.embeddingUpNat (F ⋙ G)
  have hm : mFG.inv ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map mF.hom =
      mG.inv := by
    apply (cancel_epi mFG.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [mapExtendIso_comp_hom F G K]
    simp only [mG, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  unfold sectionExtendIso CochainComplex.mapExtendHomologyIso
  dsimp only [Iso.symm, Iso.trans, Functor.mapIso]
  exact map_relation (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (q : ℤ))
    _ mFG.inv ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map mF.hom) mG.inv hm

private theorem regroup_five {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G) :
    a ≫ b ≫ c ≫ d ≫ e = (a ≫ b) ≫ c ≫ (d ≫ e) := by
  simp only [Category.assoc]

private theorem map_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {A B K : C} {T : E}
    (a : T ⟶ G.obj (F.obj A)) (f : A ⟶ B) (g : B ⟶ K) :
    a ≫ G.map (F.map (f ≫ g)) = (a ≫ G.map (F.map f)) ≫ G.map (F.map g) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem transport_equation {C : Type*} [Category C]
    {A B M N P Q PZ QZ R RZ : C}
    (m : A ⟶ B) (rI : A ⟶ M) (rJ : B ⟶ N) (nI : M ⟶ P) (nJ : N ⟶ Q)
    (sI : P ⟶ PZ) (sJ : Q ⟶ QZ) (sL : R ⟶ RZ)
    (betaN : P ⟶ R) (ellN : Q ⟶ R) (betaZ : PZ ⟶ RZ) (ellZ : QZ ⟶ RZ)
    (hn : m ≫ rJ ≫ nJ ≫ ellN = rI ≫ nI ≫ betaN)
    (hden : sJ ≫ ellZ = ellN ≫ sL) (hnum : sI ≫ betaZ = betaN ≫ sL) :
    m ≫ (rJ ≫ nJ ≫ sJ) ≫ ellZ = (rI ≫ nI ≫ sI) ≫ betaZ := by
  simp only [Category.assoc]
  rw [hden, hnum]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ sL) hn

private theorem transport_roof_comparisons {C : Type*} [Category C]
    {A B M N P Q PZ QZ R RZ : C}
    (m : A ⟶ B) (rI : A ⟶ M) (rJ : B ⟶ N) (nI : M ⟶ P) (nJ : N ⟶ Q)
    (sI : P ⟶ PZ) (sJ : Q ⟶ QZ) (sL : R ⟶ RZ)
    (betaN : P ⟶ R) (ellN : Q ⟶ R) (betaZ : PZ ⟶ RZ) (ellZ : QZ ⟶ RZ)
    (uI : A ⟶ PZ) (uJ : B ⟶ QZ)
    (hI : uI = rI ≫ nI ≫ sI) (hJ : uJ = rJ ≫ nJ ≫ sJ)
    (hn : m ≫ rJ ≫ nJ ≫ ellN = rI ≫ nI ≫ betaN)
    (hden : sJ ≫ ellZ = ellN ≫ sL) (hnum : sI ≫ betaZ = betaN ≫ sL) :
    m ≫ uJ ≫ ellZ = uI ≫ betaZ := by
  rw [hI, hJ]
  exact transport_equation m rI rJ nI nJ sI sJ sL betaN ellN betaZ ellZ hn hden hnum

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom
attribute [local irreducible] moduleCohomologyFMap sectionExtendIso

private theorem pushforward_sectionExtendIso_naturality
    {X Z : Scheme.{u}} (v : Z ⟶ X) (U : X.Opens)
    (J : CochainComplex Z.Modules ℕ) (L : CochainComplex X.Modules ℕ)
    (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J ⟶ L)
    (q : ℕ) :
    let E := RingedSpace.openModuleSections X.toRingedSpace U
    let Γ := E.mapHomologicalComplex (ComplexShape.up ℤ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (q : ℤ)
    (sectionExtendIso (RingedSpace.openModuleSections Z.toRingedSpace (v ⁻¹ᵁ U)) J q).hom ≫
        H.map (Γ.map ((J.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
          HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat)) =
      HomologicalComplex.homologyMap
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map ell) q ≫
          (sectionExtendIso E L q).hom := by
  intro E Γ H
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
    Scheme.Modules.instAbelian] at *
  let : E.Additive := inferInstanceAs
    (RingedSpace.openModuleSections X.toRingedSpace U).Additive
  let : (pushforward v).Additive := inferInstanceAs (pushforward v).Additive
  let sJ := sectionExtendIso (RingedSpace.openModuleSections Z.toRingedSpace (v ⁻¹ᵁ U)) J q
  have hcomp := map_map_comp Γ H sJ.hom
    (J.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom
    (HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat)
  refine hcomp.trans ?_
  exact (congrArg (fun z ↦ z ≫ H.map (Γ.map
    (HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat)))
      (sectionExtendIso_comp (pushforward v) E J q
        (hG := inferInstanceAs E.Additive))).trans (sectionExtendIso_naturality E ell q)

private theorem squareResolutionCohomologyIso_hom {X : Scheme.{u}} {F : X.Modules}
    (I : InjectiveResolution F) (U : X.Opens) (R : RestrictedResolutionSections I U)
    (q : ℕ) :
    let r := (forget₂ _ AddCommGrpCat.{u}).mapIso
      ((show InjectiveResolution (C := SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace)) ((restrictFunctor U.ι).obj F) from
          R.resolution).isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) q) ≪≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc q).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
    (squareResolutionCohomologyIso I U R q).hom =
      r.hom ≫ HomologicalComplex.homologyMap R.sections.hom q ≫
        (sectionExtendIso (RingedSpace.openModuleSections X.toRingedSpace U)
          I.cocomplex q).hom := by
  intro r
  unfold squareResolutionCohomologyIso
  dsimp only [r]
  unfold sectionExtendIso CochainComplex.mapExtendHomologyIso
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso]
  exact regroup_five (C := AddCommGrpCat.{u}) _ _ _ _ _

-- The proof transports the natural-indexed section equation through fixed integer models.
/-- Restriction of an augmented roof computes the classical h-map on an arbitrary open.
There is one scheme morphism, no direct-image square, and no total derived functor. -/
theorem restrictedCoefficient_roof {X Z : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ) (hL : ∀ n : ℕ, Injective (L.X n))
    (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L)
    (hell : QuasiIso ell) (beta : I.cocomplex ⟶ L)
    (hbeta : I.ι.f 0 ≫ beta.f 0 = φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0)
    (U : X.Opens) (R : RestrictedResolutionSections I U)
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ U)) (q : ℕ) :
    let Γ := (RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℤ) (q : ℤ)
    let ellZ := (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
      HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat
    let betaZ := HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat
    moduleCohomologyFMap (v.resLE U (v ⁻¹ᵁ U) le_rfl)
      (restrictedDirectImageMap v φ U) q ≫
      (squareResolutionCohomologyIso J (v ⁻¹ᵁ U) R' q).hom ≫ H.map (Γ.map ellZ) =
    (squareResolutionCohomologyIso I U R q).hom ≫ H.map (Γ.map betaZ) := by
  intro Γ H ellZ betaZ
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
    Scheme.Modules.instAbelian] at *
  let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive (v ⁻¹ᵁ U).toScheme.toRingedSpace
  let E := RingedSpace.openModuleSections X.toRingedSpace U
  let : E.Additive := inferInstanceAs
    (RingedSpace.openModuleSections X.toRingedSpace U).Additive
  let : (pushforward v).Additive := inferInstanceAs (pushforward v).Additive
  let EN := E.mapHomologicalComplex (ComplexShape.up ℕ)
  let HN := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q
  let rI := (forget₂ _ AddCommGrpCat.{u}).mapIso
    ((show InjectiveResolution (C := SheafOfModules.{u}
        (moduleRings U.toScheme.toRingedSpace)) ((restrictFunctor U.ι).obj F) from
        R.resolution).isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) q) ≪≫
    (((RingedSpace.globalSectionsComplex R.resolution).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm
  let rJ := (forget₂ _ AddCommGrpCat.{u}).mapIso
    ((show InjectiveResolution (C := SheafOfModules.{u}
        (moduleRings (v ⁻¹ᵁ U).toScheme.toRingedSpace))
          ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) from R'.resolution).isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (v ⁻¹ᵁ U).toScheme.toRingedSpace) q) ≪≫
    (((RingedSpace.globalSectionsComplex R'.resolution).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm
  let sI := sectionExtendIso E I.cocomplex q
  let sJ := sectionExtendIso
    (RingedSpace.openModuleSections Z.toRingedSpace (v ⁻¹ᵁ U)) J.cocomplex q
  let sL := sectionExtendIso E L q
  have hI : (squareResolutionCohomologyIso I U R q).hom =
      rI.hom ≫ HN.map R.sections.hom ≫ sI.hom :=
    squareResolutionCohomologyIso_hom I U R q
  have hJ : (squareResolutionCohomologyIso J (v ⁻¹ᵁ U) R' q).hom =
      rJ.hom ≫ HN.map R'.sections.hom ≫ sJ.hom :=
    squareResolutionCohomologyIso_hom J (v ⁻¹ᵁ U) R' q
  have hβ : sI.hom ≫ H.map (Γ.map betaZ) = HN.map (EN.map beta) ≫ sL.hom :=
    sectionExtendIso_naturality E beta q
  have hdenom : sJ.hom ≫ H.map (Γ.map ellZ) = HN.map (EN.map ell) ≫ sL.hom :=
    pushforward_sectionExtendIso_naturality v U J.cocomplex L ell q
  have hn := restrictedCoefficient_natRoof v F G φ I J L hL ell hell beta hbeta U R R' q
  let m := moduleCohomologyFMap (v.resLE U (v ⁻¹ᵁ U) le_rfl)
    (restrictedDirectImageMap v φ U) q
  exact transport_roof_comparisons m rI.hom rJ.hom
    (HN.map R.sections.hom) (HN.map R'.sections.hom) sI.hom sJ.hom sL.hom
    (HN.map (EN.map beta)) (HN.map (EN.map ell)) (H.map (Γ.map betaZ)) (H.map (Γ.map ellZ))
    (squareResolutionCohomologyIso I U R q).hom
    (squareResolutionCohomologyIso J (v ⁻¹ᵁ U) R' q).hom hI hJ hn hdenom hβ

end AlgebraicGeometry
