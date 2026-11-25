/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # Represented evaluation on homotopy classes

Source: Stacks Project, Tags 03Q8, 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Underived restricted sections, applied termwise below.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso). -/
noncomputable abbrev underivedSections {Y : Scheme.{v}} (W : Y.Etale) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1} ⥤ AddCommGrpCat.{v + 1} :=
  upperStar AddCommGrpCat.{v + 1} W.hom ⋙
    Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}

/-- Zeroth homology of the sections complex of a single sheaf.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso). -/
noncomputable def underivedSingleIso {Y : Scheme.{v}} (W : Y.Etale)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj A)).homology 0 ≅
        (underivedSections W).obj A :=
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (underivedSections W) (.up ℤ) 0).app A) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _

/-- Evaluate a chain map at the represented identity and then pass to homology.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso). -/
noncomputable def chainEvaluation {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale)
    (I : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (f : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)) ⟶ I) :
    (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
       (.up ℤ)).obj I).homology 0 :=
  HomologicalComplex.homologyMap
      (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
         (.up ℤ)).map f) 0
    ((underivedSingleIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))).inv (generator h U))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def representedEquiv {S Y : Scheme.{v}} (h : Y ⟶ S)
    (U : S.Etale) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U) ⟶ G) ≃
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).homEquiv _ G).trans
    (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{v + 1}).homEquiv
      _ _).trans
      (((AddCommGrpCat.adj.whiskerRight (C := S.Etaleᵒᵖ)).homEquiv _ _).trans
        uliftYonedaEquiv))

set_option backward.isDefEq.respectTransparency false in
private lemma representedEquiv_apply {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (f : (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U) ⟶ G) :
    representedEquiv h U G f =
      (sectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) G).hom
        ((underivedSections ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).map f
          (generator h U)) := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)
  have hn :
      (underivedSections W).map f ≫ (sectionsIso W G).hom =
        (sectionsIso W A).hom ≫ f.hom.app (op W) := by
    dsimp [underivedSections, sectionsIso]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc,
      (upperStarIsoLocalizationRestriction AddCommGrpCat.{v + 1} W.hom W.prop).hom.naturality,
      Functor.map_comp_assoc]
    rw [(Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale W.left)).hom.naturality_assoc]
    dsimp only [A]
    congr 1
    congr 1
    exact (f.hom.naturality _).symm
  have hn' := ConcreteCategory.congr_hom hn (generator h U)
  change representedEquiv h U G f = (sectionsIso W G).hom
    ((underivedSections W).map f (generator h U))
  simp only [ConcreteCategory.comp_apply] at hn'
  erw [hn']
  dsimp only [generator]
  change _ = f.hom.app (op W) ((sectionsIso W A).hom ((sectionsIso W A).inv _))
  rw [Iso.inv_hom_id_apply]
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).homEquiv _ G f).hom.app
      (op U) _ = _
  rw [Adjunction.homEquiv_unit]
  rfl

private noncomputable def evaluationEquiv {S Y : Scheme.{v}} (h : Y ⟶ S)
    (U : S.Etale) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U) ⟶ G) ≃+
      (underivedSections ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).obj G where
  toEquiv := (representedEquiv h U G).trans
    (sectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
      G).symm.addCommGroupIsoToAddEquiv.toEquiv
  map_add' f g := by
    change (sectionsIso _ G).inv (representedEquiv h U G (f + g)) =
      (sectionsIso _ G).inv (representedEquiv h U G f) +
        (sectionsIso _ G).inv (representedEquiv h U G g)
    erw [representedEquiv_apply, representedEquiv_apply, representedEquiv_apply]
    simp only [Iso.hom_inv_id_apply, Functor.map_add]
    rfl

private lemma evaluationEquiv_apply {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (f : (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U) ⟶ G) :
    evaluationEquiv h U G f =
      (underivedSections ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).map f
        (generator h U) := by
  change (sectionsIso _ G).inv (representedEquiv h U G f) = _
  erw [representedEquiv_apply]
  exact Iso.hom_inv_id_apply _ _

private lemma evaluationEquiv_naturality {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale)
    {G G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}} (g : G ⟶ G')
    (f : (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U) ⟶ G) :
    evaluationEquiv h U G' (f ≫ g) =
      (underivedSections ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).map g
        (evaluationEquiv h U G f) := by
  simp only [evaluationEquiv_apply, Functor.map_comp, ConcreteCategory.comp_apply]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionsComplexIso {S Y : Scheme.{v}} (h : Y ⟶ S)
    (U : S.Etale)
    (I : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))) I ≅
      (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
        (.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans
      (evaluationEquiv h U (I.X n))).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
          a i (zero_add i)
        change (underivedSections _).map (I.d i j)
            (evaluationEquiv h U (I.X i)
              (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add i)
                (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)))) =
          evaluationEquiv h U (I.X j)
            (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
              (CochainComplex.HomComplex.δ i j
                (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i))))
        simp only [CochainComplex.HomComplex.Cochain.δ_fromSingleMk, zero_add,
          CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
        exact (evaluationEquiv_naturality h U (I.d i j) a).symm)

private noncomputable def homClassIso
    {C : Type*} [Category C] [Abelian C] (K L : CochainComplex C ℤ) :
    AddCommGrpCat.of (CochainComplex.HomComplex.CohomologyClass K L 0) ≅
      AddCommGrpCat.of ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj L) :=
  CochainComplex.HomComplex.CohomologyClass.homAddEquiv.toAddCommGrpIso ≪≫
    (preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient C (.up ℤ)).obj K))).mapIso
      ((HomotopyCategory.quotient C (.up ℤ)).mapIso
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app L))

private lemma homClassIso_mk
    {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (homClassIso K L).hom
        (CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.ofHom f)) =
      (HomotopyCategory.quotient C (.up ℤ)).map f := by
  change (HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.ofHom f)) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L) = _
  rw [← Functor.map_comp]
  congr 1
  ext i
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.HomComplex.Cochain.rightShift_v]

set_option backward.isDefEq.respectTransparency false in
private lemma sectionsComplexIso_evaluation {S Y : Scheme.{v}} (h : Y ⟶ S)
    (U : S.Etale)
    (I : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (f : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)) ⟶ I) :
    HomologicalComplex.homologyMap (sectionsComplexIso h U I).hom 0
      ((CochainComplex.HomComplex.leftHomologyData _ I 0).homologyIso.inv
        (CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.ofHom f))) =
      chainEvaluation h U I f := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)
  let R := underivedSections W
  let S := (CochainComplex.singleFunctor _ 0).obj A
  let P := (R.mapHomologicalComplex (.up ℤ)).obj S
  let H := CochainComplex.HomComplex S I
  let D := CochainComplex.HomComplex.leftHomologyData S I 0
  let a := CochainComplex.HomComplex.Cocycle.ofHom f
  let c := (sectionsComplexIso h U I).hom
  let t := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app A
  let b := (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (R.obj A)).inv
    (generator h U)
  have ha : D.homologyIso.inv (CochainComplex.HomComplex.CohomologyClass.mk a) =
      H.homologyπ 0 (D.cyclesIso.inv a) := by
    exact ConcreteCategory.congr_hom D.π_comp_homologyIso_inv a
  have hb : (underivedSingleIso W A).inv (generator h U) =
      P.homologyπ 0 (HomologicalComplex.cyclesMap t.inv 0 b) := by
    dsimp only [underivedSingleIso, Iso.trans_inv, Functor.mapIso_inv,
      HomologicalComplex.homologyFunctor_map]
    have h₁ := ConcreteCategory.congr_hom
      (HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv
        (.up ℤ) 0 (R.obj A)) b
    simp only [ConcreteCategory.comp_apply] at h₁
    dsimp only [b] at h₁
    rw [Iso.inv_hom_id_apply] at h₁
    change HomologicalComplex.homologyMap t.inv 0
      ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (R.obj A)).inv
        (generator h U)) = _
    rw [h₁]
    exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t.inv 0) b
  have hc : HomologicalComplex.cyclesMap c 0 (D.cyclesIso.inv a) =
      HomologicalComplex.cyclesMap ((R.mapHomologicalComplex (.up ℤ)).map f) 0
        (HomologicalComplex.cyclesMap t.inv 0 b) := by
    apply (AddCommGrpCat.mono_iff_injective
      (((R.mapHomologicalComplex (.up ℤ)).obj I).iCycles 0)).mp inferInstance
    have hc₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i c 0)
      (D.cyclesIso.inv a)
    have hc₂ := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i ((R.mapHomologicalComplex (.up ℤ)).map f) 0)
        (HomologicalComplex.cyclesMap t.inv 0 b)
    have hc₃ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t.inv 0) b
    have hd := ConcreteCategory.congr_hom D.cyclesIso_inv_comp_iCycles a
    simp only [ConcreteCategory.comp_apply] at hc₁ hc₂ hc₃ hd
    change P.iCycles 0 (HomologicalComplex.cyclesMap t.inv 0 b) =
      t.inv.f 0 (((CochainComplex.singleFunctor _ 0).obj (R.obj A)).iCycles 0 b) at hc₃
    change H.iCycles 0 (D.cyclesIso.inv a) = (a : CochainComplex.HomComplex.Cochain S I 0)
      at hd
    rw [hc₁, hc₂]
    erw [hc₃, hd]
    change evaluationEquiv h U (I.X 0)
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ))
          (CochainComplex.HomComplex.Cochain.ofHom f)) =
      R.map (f.f 0) (t.inv.f 0
        (((CochainComplex.singleFunctor _ 0).obj (R.obj A)).iCycles 0 b))
    have ht : t.inv.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (R.obj A)).hom ≫
          R.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv :=
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self R (.up ℤ) 0 A
    rw [ht]
    dsimp only [b]
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (.up ℤ) 0 (R.obj A))
        (generator h U)
    simp only [ConcreteCategory.comp_apply] at hi
    erw [hi]
    simp only [ConcreteCategory.comp_apply]
    rw [evaluationEquiv_apply]
    change R.map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ f.f 0)
      (generator h U) = _
    rw [Functor.map_comp]
    rfl
  change HomologicalComplex.homologyMap c 0 (D.homologyIso.inv
    (CochainComplex.HomComplex.CohomologyClass.mk a)) = _
  rw [ha]
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality c 0)
    (D.cyclesIso.inv a)
  simp only [ConcreteCategory.comp_apply] at h₁
  rw [h₁, hc]
  dsimp only [chainEvaluation]
  change _ = HomologicalComplex.homologyMap ((R.mapHomologicalComplex (.up ℤ)).map f) 0
    ((underivedSingleIso W A).inv (generator h U))
  rw [hb]
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality ((R.mapHomologicalComplex (.up ℤ)).map f) 0)
      (HomologicalComplex.cyclesMap t.inv 0 b)).symm

/-- The free represented sheaf identifies homotopy classes with section cohomology.
Source: Stacks Project, Tag 03Q8; Cohomology on Sites, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso).

Proof: the inverse-image/direct-image adjunction, the sheafification adjunction,
free-abelian adjunction and Yoneda identify maps from the pulled-back free represented
sheaf to each term of I with its sections over U times Y. The map is evaluation at
`generator h U`: this follows from the unit formula for the first adjunction and the
identity formula for Yoneda. These additive equivalences commute with every differential.
Using the from-single cochain equivalence gives a chain isomorphism from the Hom complex
of the degree-zero single sheaf into I to the termwise restricted-sections complex.
Zeroth Hom-complex cohomology is homotopy classes of maps. Apply zeroth homology to the
chain isomorphism. On a chain map this is exactly `chainEvaluation`, since the
single-complex homology isomorphism sends the identity generator to its class.
The argument applies to arbitrary complexes, including the zero complex, and to the
empty pullback, where both groups are zero. No injective resolution is used here. -/
theorem exists_rawRestrictedHomotopySectionsIso {S Y : Scheme.{v}}
    (h : Y ⟶ S) (U : S.Etale)
    (I : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    ∃ e : AddCommGrpCat.of
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))) ⟶
          (HomotopyCategory.quotient _ (.up ℤ)).obj I) ≅
        (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
           (.up ℤ)).obj I).homology 0,
      ∀ f, e.hom ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
        chainEvaluation h U I f := by
  let S := (CochainComplex.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))
  let e := (homClassIso S I).symm ≪≫
    (CochainComplex.HomComplex.leftHomologyData S I 0).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso (sectionsComplexIso h U I)
  refine ⟨e, fun f ↦ ?_⟩
  have hf : (homClassIso S I).hom
      (CochainComplex.HomComplex.CohomologyClass.mk
        (CochainComplex.HomComplex.Cocycle.ofHom f)) =
      (HomotopyCategory.quotient _ (.up ℤ)).map f := homClassIso_mk f
  have hi := congrArg (fun x ↦ (homClassIso S I).inv x) hf
  simp only [Iso.hom_inv_id_apply] at hi
  change HomologicalComplex.homologyMap (sectionsComplexIso h U I).hom 0
    ((CochainComplex.HomComplex.leftHomologyData S I 0).homologyIso.inv
      ((homClassIso S I).inv ((HomotopyCategory.quotient _ (.up ℤ)).map f))) = _
  rw [← hi]
  exact sectionsComplexIso_evaluation h U I f

end AlgebraicGeometry.Etale.RawRestrictedComparison
