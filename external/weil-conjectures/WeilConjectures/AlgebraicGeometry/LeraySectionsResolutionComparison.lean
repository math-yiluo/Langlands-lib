/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ConcreteCategory

/-! # Resolution comparison for sections of a direct image

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX
(blueprint: lem-pc-leray-sections-resolution-comparison).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false in
/-- Restriction along Opens.map_top identifies the underlying abelian groups of sections,
  naturally in the module sheaf.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private def sectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ forget₂ _ AddCommGrpCat) ≅
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace) ⋙ forget₂ _ AddCommGrpCat) :=
  NatIso.ofComponents
    (fun M ↦ M.val.presheaf.mapIso (eqToIso (congrArg op (Opens.map_top f.base).symm)))
    (fun g ↦ (((PresheafOfModules.toPresheaf _).map g.val).naturality
      (eqToHom (congrArg op (Opens.map_top f.base).symm))).symm)
set_option backward.isDefEq.respectTransparency false in
/-- Exact forgetting of scalars commutes with cochain homology.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private def homologyForgetIso {R : Type u} [Ring R] (q : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) q ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q ⋙
        forget₂ _ AddCommGrpCat :=
  NatIso.ofComponents
    (fun K ↦ (K.sc q).mapHomologyIso (forget₂ _ AddCommGrpCat))
    (fun g ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ q).map g)
        (forget₂ (ModuleCat R) AddCommGrpCat))

set_option backward.isDefEq.respectTransparency false in
/-- The natural homology comparison on all cochain complexes, before choosing resolutions.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private def sectionsHomologyIso {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℕ) q ⋙ forget₂ _ AddCommGrpCat ≅
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
      RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℕ) q ⋙ forget₂ _ AddCommGrpCat :=
  (Functor.isoWhiskerLeft
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex _)
      (homologyForgetIso q).symm) ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (sectionsIso f) (.up ℕ))
      (HomologicalComplex.homologyFunctor _ (.up ℕ) q) ≪≫
    Functor.isoWhiskerLeft
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex _)
      (homologyForgetIso q)

set_option backward.isDefEq.respectTransparency false in
/-- Conjugate the comparison of section homologies by the canonical resolution identifications.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private def resolutionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution F) :
    (forget₂ _ AddCommGrpCat).obj ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≅
      (forget₂ _ AddCommGrpCat).obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerived q).obj F) :=
  (forget₂ _ AddCommGrpCat).mapIso
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q) ≪≫
    (sectionsHomologyIso f q).app I.cocomplex ≪≫
    (forget₂ _ AddCommGrpCat).mapIso
      (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace) q).symm

-- Conjugation by resolution isomorphisms has several dependent functor compositions.
set_option backward.isDefEq.respectTransparency false in
/-- A cochain map extending a coefficient morphism intertwines the resolution comparisons.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem resolutionIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    {F F' : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (φ : F ⟶ F')
    (I : InjectiveResolution F) (J : InjectiveResolution F')
    (g : I.cocomplex ⟶ J.cocomplex) (hg : I.ι.f 0 ≫ g.f 0 = φ ≫ J.ι.f 0) :
    (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ) ≫
      (resolutionIso f q J).hom =
    (resolutionIso f q I).hom ≫
      (forget₂ _ AddCommGrpCat).map
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerived q).map φ) := by
  let A := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let B := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let U := forget₂ (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let V := forget₂ (ModuleCat ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  have hA := congrArg U.map (InjectiveResolution.isoRightDerivedObj_hom_naturality φ I J g hg A q)
  have hB := congrArg V.map (InjectiveResolution.isoRightDerivedObj_inv_naturality φ I J g hg B q)
  simp only [Functor.map_comp] at hA hB
  have hα := (sectionsHomologyIso f q).hom.naturality g
  change U.map ((A.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℕ) q).map g) ≫
        ((sectionsHomologyIso f q).app J.cocomplex).hom =
      ((sectionsHomologyIso f q).app I.cocomplex).hom ≫
        V.map ((B.mapHomologicalComplex (.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (.up ℕ) q).map g) at hα
  dsimp only [resolutionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    RingedSpace.moduleCohomology]
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hα]
  simp only [A, B, U, V, Functor.comp_map] at hB ⊢
  rw [← hB]

set_option backward.isDefEq.respectTransparency false in
/-- Construct the natural derived comparison using Mathlib's chosen injective resolutions.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private def derivedSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ≅
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerived q ⋙
          forget₂ _ AddCommGrpCat) :=
  NatIso.ofComponents (fun F ↦ resolutionIso f q (injectiveResolution F))
    (fun φ ↦ resolutionIso_naturality f q φ _ _
      (InjectiveResolution.desc φ _ _) (InjectiveResolution.desc_commutes_zero φ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison for exact forgetting of scalars respects the cycle class map.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem forget_homologyπ {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) :
    (S.mapCyclesIso (forget₂ _ AddCommGrpCat)).hom ≫
        (forget₂ _ AddCommGrpCat).map S.homologyπ =
      (S.map (forget₂ _ AddCommGrpCat)).homologyπ ≫
        (S.mapHomologyIso (forget₂ _ AddCommGrpCat)).hom := by
  let U := forget₂ (ModuleCat R) AddCommGrpCat
  let h := S.homologyData.left
  rw [h.mapCyclesIso_eq U, h.mapHomologyIso_eq U]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [(h.map U).homologyπ_comp_homologyIso_hom_assoc]
  have hπ := congrArg U.map h.π_comp_homologyIso_inv
  simp only [Functor.map_comp] at hπ
  rw [← hπ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Comparison extending the identity gives the same isomorphism on any supplied resolution.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem derivedSectionsIso_app {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution F) :
    (derivedSectionsIso f q).hom.app F = (resolutionIso f q I).hom := by
  have h := resolutionIso_naturality f q (𝟙 F) (injectiveResolution F) I
    (InjectiveResolution.desc (𝟙 F) I (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero (𝟙 F) I (injectiveResolution F))
  change (resolutionIso f q (injectiveResolution F)).hom = (resolutionIso f q I).hom
  have hA := (RingedSpace.moduleCohomology X.toRingedSpace q).map_id F
  have hB := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerived q |>.map_id F
  rw [hA, hB] at h
  rw [(forget₂ (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat).map_id _,
    (forget₂ (ModuleCat ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat).map_id _, Category.id_comp, Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse homology comparison represents a class by the corresponding forgotten cycle.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem forget_homologyπ_inv {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) :
    (forget₂ _ AddCommGrpCat).map S.homologyπ ≫
        (S.mapHomologyIso (forget₂ _ AddCommGrpCat)).inv =
      (S.mapCyclesIso (forget₂ _ AddCommGrpCat)).inv ≫
        (S.map (forget₂ _ AddCommGrpCat)).homologyπ := by
  rw [← cancel_epi (S.mapCyclesIso (forget₂ _ AddCommGrpCat)).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, forget_homologyπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse cycle comparison respects the inclusion into the degree term.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem forget_iCycles_inv {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) :
    (S.mapCyclesIso (forget₂ _ AddCommGrpCat)).inv ≫
        (S.map (forget₂ _ AddCommGrpCat)).iCycles =
      (forget₂ _ AddCommGrpCat).map S.iCycles := by
  rw [← S.mapCyclesIso_hom_iCycles (forget₂ _ AddCommGrpCat), Iso.inv_hom_id_assoc]

-- The comparison combines homology and cycles in two module categories and abelian groups.
set_option backward.isDefEq.respectTransparency false in
/-- A termwise restriction carries the class of a cycle to the class of the restricted cycle.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem sectionsHomologyIso_cycle {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ) :
    let S := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (.up ℕ)).obj K
    let T := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
      RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex (.up ℕ)).obj K
    ∀ (s : S.cycles q) (t : T.cycles q),
      (K.X q).val.presheaf.map (eqToHom (congrArg op (Opens.map_top f.base).symm))
        (S.iCycles q s) = T.iCycles q t →
      (sectionsHomologyIso f q).hom.app K (S.homologyπ q s) = T.homologyπ q t := by
  intro S T s t ht
  let U := forget₂ (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let V := forget₂ (ModuleCat ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let SU := (U.mapHomologicalComplex (.up ℕ)).obj S
  let TV := (V.mapHomologicalComplex (.up ℕ)).obj T
  let a : SU ≅ TV := (NatIso.mapHomologicalComplex (sectionsIso f) (.up ℕ)).app K
  let bS := (S.sc q).mapCyclesIso U
  let bT := (T.sc q).mapCyclesIso V
  have hS : SU.iCycles q (bS.inv s) = S.iCycles q s :=
    ConcreteCategory.congr_hom (forget_iCycles_inv (S.sc q)) s
  have hT : TV.iCycles q (bT.inv t) = T.iCycles q t :=
    ConcreteCategory.congr_hom (forget_iCycles_inv (T.sc q)) t
  have hab : HomologicalComplex.cyclesMap a.hom q (bS.inv s) = bT.inv t := by
    apply (AddCommGrpCat.mono_iff_injective (TV.iCycles q)).mp inferInstance
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i a.hom q)
      (bS.inv s)
    change TV.iCycles q (HomologicalComplex.cyclesMap a.hom q (bS.inv s)) =
      a.hom.f q (SU.iCycles q (bS.inv s)) at h
    rw [h, hS, hT]
    exact ht
  have hpS := ConcreteCategory.congr_hom (forget_homologyπ_inv (S.sc q)) s
  have hpT := ConcreteCategory.congr_hom (forget_homologyπ (T.sc q)) (bT.inv t)
  have ha := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality a.hom q)
    (bS.inv s)
  change HomologicalComplex.homologyMap a.hom q (SU.homologyπ q (bS.inv s)) =
    TV.homologyπ q (HomologicalComplex.cyclesMap a.hom q (bS.inv s)) at ha
  rw [hab] at ha
  change ((T.sc q).mapHomologyIso V).hom
      (HomologicalComplex.homologyMap a.hom q
        (((S.sc q).mapHomologyIso U).inv (S.homologyπ q s))) = T.homologyπ q t
  change ((S.sc q).mapHomologyIso U).inv (S.homologyπ q s) =
    SU.homologyπ q (bS.inv s) at hpS
  change T.homologyπ q (bT.hom (bT.inv t)) =
    ((T.sc q).mapHomologyIso V).hom (TV.homologyπ q (bT.inv t)) at hpT
  rw [hpS, ha]
  simpa only [Iso.inv_hom_id_apply] using hpT.symm

-- Conjugating the cycle formula unfolds the resolution and section comparisons.
set_option backward.isDefEq.respectTransparency false in
/-- Transport the cycle formula through the canonical resolution isomorphisms.
Source: Stacks Project, Cohomology, Tag 01F2 (lemma-before-Leray and
remark-elucidate-lemma). -/
private theorem derivedSectionsIso_cycle {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution F) :
    let S := RingedSpace.globalSectionsComplex I
    let B := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
      RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let T := (B.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    ∀ (s : S.cycles q) (t : T.cycles q),
      (I.cocomplex.X q).val.presheaf.map
        (eqToHom (congrArg op (Opens.map_top f.base).symm)) (S.iCycles q s) =
          T.iCycles q t →
      (derivedSectionsIso f q).hom.app F
        ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
          (S.homologyπ q s)) =
        (I.isoRightDerivedObj B q).inv (T.homologyπ q t) := by
  intro S B T s t ht
  rw [derivedSectionsIso_app f q I]
  change (I.isoRightDerivedObj B q).inv
      ((sectionsHomologyIso f q).hom.app I.cocomplex
        ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).hom
          ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
            (S.homologyπ q s)))) = _
  rw [Iso.inv_hom_id_apply]
  exact congrArg (fun x ↦ (I.isoRightDerivedObj B q).inv x)
    (sectionsHomologyIso_cycle f q I.cocomplex s t ht)

end

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation preserves the cycle kernel. Restriction of an upstairs cycle has
zero differential by naturality, so it lifts through this preserved kernel. -/
private theorem leray_sections_cycle_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F) (q : ℕ)
    (s : (RingedSpace.globalSectionsComplex I).cycles q) :
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let K := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    ∃ z : G.obj (K.cycles q),
      (I.cocomplex.X q).val.presheaf.map
        (eqToHom (congrArg op (Opens.map_top f.base).symm))
        ((RingedSpace.globalSectionsComplex I).iCycles q s) = G.map (K.iCycles q) z := by
  dsimp only
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let K := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let : PreservesFiniteLimits G := inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
  have hlim := KernelFork.mapIsLimit _ (K.sc q).cyclesIsKernel G
  let e : T.cycles q ≅ G.obj (K.cycles q) := ((T.sc q).isoCyclesOfIsLimit hlim).symm
  let x := (I.cocomplex.X q).val.presheaf.map
    (eqToHom (congrArg op (Opens.map_top f.base).symm))
    ((RingedSpace.globalSectionsComplex I).iCycles q s)
  have hx : T.d q (q + 1) x = 0 := by
    let r := eqToHom (congrArg op (Opens.map_top f.base).symm)
    have hn := (I.cocomplex.d q (q + 1)).val.naturality r
    have hz := ConcreteCategory.congr_hom
      ((RingedSpace.globalSectionsComplex I).iCycles_d q (q + 1)) s
    have hn' := ConcreteCategory.congr_hom hn
      ((RingedSpace.globalSectionsComplex I).iCycles q s)
    change T.d q (q + 1) x =
      (I.cocomplex.X (q + 1)).val.presheaf.map r
        ((RingedSpace.globalSectionsComplex I).d q (q + 1)
          ((RingedSpace.globalSectionsComplex I).iCycles q s)) at hn'
    have hz' : (RingedSpace.globalSectionsComplex I).d q (q + 1)
        ((RingedSpace.globalSectionsComplex I).iCycles q s) = 0 := hz
    rw [hn', hz']
    exact map_zero _
  let t := T.cyclesMk x (q + 1) (by simp) hx
  refine ⟨e.hom t, ?_⟩
  have ht := T.i_cyclesMk x (q + 1) (by simp) hx
  have he' : e.hom ≫ G.map (K.iCycles q) = T.iCycles q :=
    (T.sc q).isoCyclesOfIsLimit_inv_ι hlim
  change x = (e.hom ≫ G.map (K.iCycles q)) t
  rw [he']
  exact ht.symm

-- The dependent cycle objects require unfolding termwise functor compositions.
set_option backward.isDefEq.respectTransparency false in
/-- Compare the derived composite with sections upstairs, retaining its cycle formula.
No edge map or acyclicity witness occurs in this statement.

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.
(blueprint: lem-pc-leray-sections-resolution-comparison)

Proof: Restriction along Opens.map_top identifies sections of the direct image on Y
with sections on X, naturally in the module sheaf. After forgetting scalars this is
an isomorphism, with inverse restriction along the inverse equality. Apply it in each
degree of a complex. Restriction commutes with differentials and comparison cochain
maps. Taking homology gives natural isomorphisms on the chosen injective resolutions;
conjugate by isoRightDerivedObj to obtain e. Naturality follows from the comparison
maps extending coefficient morphisms and isoRightDerivedObj naturality. For any other
injective resolution the comparison extending the identity shows the same formula.
Sections preserves the kernel defining the cycle sheaf, so each transported global
cycle has a unique lift z. Any c with the displayed inclusion equation sends z to the
transported global cycle: the inclusion into the term is monic. The homology map of
the termwise restriction sends the original cycle class to the class of c(z).
Conjugating by the resolution isomorphisms proves the last equation. In degree zero
and for zero complexes the same kernel argument applies; empty schemes introduce no
exception. The isomorphism e is determined by this formula since the cycle quotient
is epic, so the statement determines the comparison rather than an arbitrary witness.
-/
theorem leray_sections_resolution_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    ∃ e : ∀ q : ℕ,
      (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ≅
        ((D ⋙ G).rightDerived q ⋙ forget₂ _ AddCommGrpCat),
    ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (I : InjectiveResolution F)
      (s : (RingedSpace.globalSectionsComplex I).cycles q),
      let K := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      let T := ((D ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      ∃ z : G.obj (K.cycles q),
        (I.cocomplex.X q).val.presheaf.map
            (eqToHom (congrArg op (Opens.map_top f.base).symm))
            ((RingedSpace.globalSectionsComplex I).iCycles q s) = G.map (K.iCycles q) z ∧
        ∀ (c : G.obj (K.cycles q) ⟶ T.cycles q),
          c ≫ T.iCycles q = G.map (K.iCycles q) →
          (e q).hom.app F
              ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
                ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
            (I.isoRightDerivedObj (D ⋙ G) q).inv (T.homologyπ q (c z)) := by
  dsimp only
  refine ⟨fun q ↦ derivedSectionsIso f q, ?_⟩
  intro q F I s
  obtain ⟨z, hz⟩ := leray_sections_cycle_lift f F I q s
  refine ⟨z, hz, ?_⟩
  intro c hc
  apply derivedSectionsIso_cycle f q I s (c z)
  exact hz.trans (ConcreteCategory.congr_hom hc z).symm

end AlgebraicGeometry
