/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration
import WeilConjectures.CategoryTheory.BrownRepresentabilityHomLocallySmall
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Coherator adjunction and detection by global sections

Source: Stacks Project, Tag 0B6I, final paragraph of the proof, and Derived Categories
of Schemes, `perfect-lemma-better-coherator`
(blueprint: lem-pc-dq-coherator-adjunction).

Derived global sections are expressed by their K-injective representatives: applying
`RingedSpace.globalSectionsFunctor` termwise to a K-injective complex represents RΓ.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry
/-- The inclusion of the quasi-coherent derived full subcategory on a qcqs scheme
has a right adjoint. Its adjunction supplies the natural Hom bijection.
Source: Stacks Project, Tag 0B6I, final proof paragraph, and
`perfect-lemma-better-coherator` (blueprint: lem-pc-dq-coherator-adjunction).

Proof: compact generation (`lem-pc-derived-qcoh-compact-generation`) and coproducts
(`lem-pc-derived-qcoh-direct-sums`) hold for qcqs schemes. Ambient coproducts have
cohomology given by direct sums (`lem-pc-derived-ambient-direct-sums`). Finite sums
of quasi-coherent modules are quasi-coherent (`lem-weil-pbc-quasi-coherent-module-direct-sum`),
and their directed colimit is quasi-coherent
(`lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`). Thus ambient coproducts
lie in the full subcategory and are its coproducts, so inclusion preserves them.
The inherited triangles make inclusion exact. Brown representability
(`lem-pc-brown-representability-right-adjoint`) supplies the right adjoint. -/
theorem exists_dqCoheratorAdjunction (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ DQ_Y : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y,
      Nonempty (Adjunction (schemeDerivedQCohProperty Y).ι DQ_Y) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  obtain ⟨htri, hsums, hgen⟩ := schemeDerivedQCoh_compactlyGenerated Y
  let := htri
  let := hsums
  let : CategoryTheory.Limits.HasCoproducts.{u} (schemeDerivedCategory Y) :=
    derivedAmbientHasCoproducts Y
  have hpres : ∀ T : Type u,
      CategoryTheory.Limits.PreservesColimitsOfShape (Discrete T)
        (schemeDerivedQCohProperty Y).ι := by
    intro T
    let := schemeDerivedQCohClosedUnderCoproducts Y T
    infer_instance
  have hAdj : (schemeDerivedQCohProperty Y).ι.IsLeftAdjoint := by
    apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
    funext E
    apply propext
    change ((schemeDerivedQCohProperty Y).ι.op ⋙ yoneda.obj E).IsRepresentable ↔ True
    exact ⟨fun _ ↦ trivial, fun _ ↦
      brownHomRepresentabilityLocallySmall (schemeDerivedQCohProperty Y).ι hgen hpres E⟩
  exact ⟨_, ⟨Adjunction.ofIsLeftAdjoint (schemeDerivedQCohProperty Y).ι⟩⟩


/-- Every shift O_Y[-i] is in the quasi-coherent full subcategory.
Source: Stacks Project, Tag 0B6I, final proof paragraph
(blueprint: lem-pc-dq-coherator-adjunction).

Proof: the shifted complex has only one nonzero cohomology sheaf, namely O_Y,
which is quasi-coherent; every other cohomology sheaf is zero and quasi-coherent.
Use `lemma-coherent-base-change-invertible-sheaves` to conclude. -/
theorem structureSheaf_shift_is_derivedQCoh (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] (i : ℤ) :
    schemeDerivedQCohProperty Y
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦-i⟧) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let M : C := SheafOfModules.unit (moduleRings Y.toRingedSpace)
  let e := ((DerivedCategory.singleFunctors C).shiftIso (-i) i 0 (by simp)).app M
  classical
  intro n
  let H := DerivedCategory.homologyFunctor C n
  apply (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
    (H.mapIso e.symm)
  by_cases h : n = i
  · subst n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M).symm
      (by
        change (SheafOfModules.unit (moduleRings Y.toRingedSpace)).IsQuasicoherent
        exact SheafOfModules.isQuasicoherent_unit (R := moduleRings Y.toRingedSpace))
  · let eH := (DerivedCategory.homologyFunctorFactors C n).app
      ((CochainComplex.singleFunctor C i).obj M)
    have hz := HomologicalComplex.isZero_single_obj_homology (.up ℤ) i M n h
    let Z : PEmpty.{u + 1} → C := fun j ↦ PEmpty.elim j
    have hZ : (∐ Z).IsQuasicoherent :=
      @Scheme.Modules.isQuasicoherent_sigma Y _ Z (fun j ↦ PEmpty.elim j)
    have hzZ : CategoryTheory.Limits.IsZero (∐ Z) := by
      apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro j
      exact PEmpty.elim j
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      (hzZ.iso (hz.of_iso eH)) hZ

namespace DQComparisonAux

open CochainComplex HomComplex Limits in
private noncomputable def postMap
    {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ}
    (S : CochainComplex C ℤ) (f : K ⟶ L) :
    HomComplex S K ⟶ HomComplex S L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ a.comp (.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' := fun a b ↦ Cochain.add_comp _ _ _ _ }
  comm' i j hij := by
    ext a
    change δ i j (a.comp (.ofHom f) (add_zero i)) =
      (δ i j a).comp (.ofHom f) (add_zero j)
    exact δ_comp_ofHom a f j

open CochainComplex HomComplex Limits in
private def postCocycle
    {C : Type*} [Category C] [Preadditive C]
    {S K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    Cocycle S K n →+ Cocycle S L n where
  toFun a := a.postcomp f
  map_zero' := by apply Cocycle.ext; simp [Cocycle.postcomp]
  map_add' a b := by apply Cocycle.ext; simp [Cocycle.postcomp, Cochain.add_comp]

open CochainComplex HomComplex Limits in
private def postClass
    {C : Type*} [Category C] [Preadditive C]
    {S K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    CohomologyClass S K n →+ CohomologyClass S L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom S L n).comp (postCocycle f n)) (by
      rintro a ⟨m, hm, b, hb⟩
      change CohomologyClass.mk (a.postcomp f) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, b.comp (.ofHom f) (add_zero m), ?_⟩
      rw [δ_comp_ofHom, hb]
      rfl)

open CochainComplex HomComplex Limits in
private lemma postClass_mk
    {C : Type*} [Category C] [Preadditive C]
    {S K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) (a : Cocycle S K n) :
    postClass f n (.mk a) = .mk (a.postcomp f) := rfl

open CochainComplex HomComplex Limits in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def postHomologyData
    {C : Type*} [Category C] [Preadditive C]
    {S K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (postMap S f))
      (leftHomologyData S K n) (leftHomologyData S L n) where
  φK := AddCommGrpCat.ofHom (postCocycle f n)
  φH := AddCommGrpCat.ofHom (postClass f n)
  commi := by ext a; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData S L n).i).1
    rw [Category.assoc]
    change _ ≫ ((leftHomologyData S K n).i ≫ (postMap S f).f n) = _
    rw [← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((postMap S f).comm _ _).symm
  commπ := by ext a; rfl

open CochainComplex HomComplex Limits in
set_option backward.isDefEq.respectTransparency false in
private lemma homologyClass_naturality
    {C : Type*} [Category C] [Preadditive C]
    {S K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap (postMap S f) n ≫
        (leftHomologyData S L n).homologyIso.hom =
      (leftHomologyData S K n).homologyIso.hom ≫
        AddCommGrpCat.ofHom (postClass f n) := by
  have h := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (postMap S f))
    (leftHomologyData S K n) (leftHomologyData S L n)
  rw [(postHomologyData f n).leftHomologyMap'_eq] at h
  exact h.symm

end DQComparisonAux

private noncomputable def unitSectionsEquiv (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    (SheafOfModules.unit (moduleRings Y.toRingedSpace) ⟶ M) ≃+
      (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M where
  toFun f := (M.unitHomEquiv f).val (Opposite.op ⊤)
  invFun a := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      rfl))
  left_inv f := by
    apply M.unitHomEquiv.injective
    apply Subtype.ext
    funext U
    simp only [Equiv.apply_symm_apply]
    exact (M.unitHomEquiv f).property _
  right_inv a := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val (Opposite.op ⊤) = a
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 _) a = a
    simp
  map_add' f g := by
    change (f.val.app (Opposite.op ⊤) + g.val.app (Opposite.op ⊤))
      (1 : (moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤)) = _
    rfl

open CochainComplex HomComplex in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def unitHomComplexSectionsIso (Y : Scheme.{u})
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))) I ≅
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace) ⋙
        forget₂ _ AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      (unitSectionsEquiv Y (I.X n))).toAddCommGrpIso) (by
      intro i j hij
      ext a
      obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
      have hn : unitSectionsEquiv Y (I.X j) (a ≫ I.d i j) =
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map (I.d i j)
            (unitSectionsEquiv Y (I.X i) a) := rfl
      simpa [HomComplex, Cochain.δ_fromSingleMk,
        Cochain.fromSingleEquiv_fromSingleMk] using! hn.symm)

open CochainComplex HomComplex in
set_option backward.isDefEq.respectTransparency false in
private lemma unitHomComplexSectionsIso_naturality (Y : Scheme.{u})
    {I J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (f : I ⟶ J) :
    DQComparisonAux.postMap ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))) f ≫
        (unitHomComplexSectionsIso Y J).hom =
      (unitHomComplexSectionsIso Y I).hom ≫
        (((RingedSpace.globalSectionsFunctor Y.toRingedSpace) ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex _).map f := by
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change unitSectionsEquiv Y (J.X n)
    ((Cochain.fromSingleEquiv (zero_add n))
      ((Cochain.fromSingleMk a (zero_add n)).comp (.ofHom f) (add_zero n))) =
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map (f.f n)
      (unitSectionsEquiv Y (I.X n)
        ((Cochain.fromSingleEquiv (zero_add n)) (Cochain.fromSingleMk a (zero_add n))))
  rw [← Cochain.fromSingleMk_postcomp]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  rfl

open CochainComplex HomComplex in
private noncomputable def unitClassSectionsIso (Y : Scheme.{u})
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (i : ℤ) :
    AddCommGrpCat.of (CohomologyClass ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))) I i) ≅
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj I).homology i :=
  (leftHomologyData _ I i).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (unitHomComplexSectionsIso Y I)

open CochainComplex HomComplex in
set_option backward.isDefEq.respectTransparency false in
private lemma unitClassSectionsIso_naturality (Y : Scheme.{u})
    {I J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (f : I ⟶ J) (i : ℤ) :
    AddCommGrpCat.ofHom (DQComparisonAux.postClass f i) ≫
        (unitClassSectionsIso Y J i).hom =
      (unitClassSectionsIso Y I i).hom ≫ HomologicalComplex.homologyMap
        (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex _).map f) i := by
  have h := DQComparisonAux.homologyClass_naturality
    (S := (CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))) f i
  have h' := congrArg ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) i).map)
    (unitHomComplexSectionsIso_naturality Y f)
  simp only [HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] at h'
  dsimp only [unitClassSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← cancel_epi (leftHomologyData _ I i).homologyIso.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h, Iso.hom_inv_id_assoc]
  exact h'

private noncomputable def isoHomAddEquiv
    {C : Type*} [Category C] [Preadditive C] {A B A' B' : C}
    (eA : A ≅ A') (eB : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') :=
  { Iso.homCongr eA eB with
    map_add' f g := by simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp] }

open CochainComplex HomComplex in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def unitClassDerivedEquiv (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [I.IsKInjective] (i : ℤ) :
    CohomologyClass ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))) I i ≃+
      ((((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦-i⟧) ⟶
            DerivedCategory.Q.obj I) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let S := (CochainComplex.singleFunctor C 0).obj
    (SheafOfModules.unit (moduleRings Y.toRingedSpace))
  let e := CohomologyClass.homAddEquiv (K := S) (L := I) (n := i)
  let eQ := AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (.up ℤ)).obj S) (I⟦i⟧))
  let eIso := isoHomAddEquiv ((DerivedCategory.quotientCompQhIso C).app S)
    (((DerivedCategory.quotientCompQhIso C).app (I⟦i⟧)) ≪≫
      (DerivedCategory.Q.commShiftIso i).app I)
  let : (shiftEquiv' (DerivedCategory C) (-i) i (neg_add_cancel i)).functor.Additive :=
    inferInstanceAs ((CategoryTheory.shiftFunctor (DerivedCategory C) (-i)).Additive)
  exact ((e.trans eQ).trans eIso).trans
    ((shiftEquiv' (DerivedCategory C) (-i) i (neg_add_cancel i)).toAdjunction.homAddEquiv
      (DerivedCategory.Q.obj S) (DerivedCategory.Q.obj I)).symm

open CochainComplex HomComplex in
set_option backward.isDefEq.respectTransparency false in
private lemma unitClassDerivedEquiv_naturality (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {I J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) (i : ℤ)
    (a : CohomologyClass ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))) I i) :
    unitClassDerivedEquiv Y J i (DQComparisonAux.postClass f i a) =
      unitClassDerivedEquiv Y I i a ≫ DerivedCategory.Q.map f := by
  have hh : CohomologyClass.toHom (DQComparisonAux.postClass f i a) =
      CohomologyClass.toHom a ≫ (HomotopyCategory.quotient _ _).map (f⟦i⟧') := by
    obtain ⟨a, rfl⟩ := a.mk_surjective
    simp only [DQComparisonAux.postClass_mk, CohomologyClass.toHom_mk,
      Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let S := (CochainComplex.singleFunctor C 0).obj
    (SheafOfModules.unit (moduleRings Y.toRingedSpace))
  let sh := shiftEquiv' (DerivedCategory C) (-i) i (neg_add_cancel i)
  -- Compute naturality before applying the adjunction's Hom equivalence.
  have hcomp :
      (DerivedCategory.quotientCompQhIso C).inv.app S ≫
        DerivedCategory.Qh.map (CohomologyClass.toHom (DQComparisonAux.postClass f i a)) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app (J⟦i⟧) ≫
        (DerivedCategory.Q.commShiftIso i).hom.app J =
      ((DerivedCategory.quotientCompQhIso C).inv.app S ≫
        DerivedCategory.Qh.map (CohomologyClass.toHom a) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app (I⟦i⟧) ≫
        (DerivedCategory.Q.commShiftIso i).hom.app I) ≫ (DerivedCategory.Q.map f)⟦i⟧' := by
    dsimp only [C, S]
    simp only [hh, Functor.map_comp, Category.assoc,
      DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
      Functor.commShiftIso_hom_naturality]
  change (sh.toAdjunction.homEquiv (DerivedCategory.Q.obj S)
    (DerivedCategory.Q.obj J)).symm
      ((DerivedCategory.quotientCompQhIso C).inv.app S ≫
        DerivedCategory.Qh.map (CohomologyClass.toHom (DQComparisonAux.postClass f i a)) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app (J⟦i⟧) ≫
        (DerivedCategory.Q.commShiftIso i).hom.app J) =
    (sh.toAdjunction.homEquiv (DerivedCategory.Q.obj S)
      (DerivedCategory.Q.obj I)).symm
        ((DerivedCategory.quotientCompQhIso C).inv.app S ≫
          DerivedCategory.Qh.map (CohomologyClass.toHom a) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app (I⟦i⟧) ≫
          (DerivedCategory.Q.commShiftIso i).hom.app I) ≫ DerivedCategory.Q.map f
  exact (congrArg (sh.toAdjunction.homEquiv (DerivedCategory.Q.obj S)
    (DerivedCategory.Q.obj J)).symm hcomp).trans
      (sh.toAdjunction.homEquiv_naturality_right_symm _ (DerivedCategory.Q.map f))

/-- Global degree-i cohomology of a K-injective representative is the derived Hom
from O_Y[-i], as an additive group.
Source: Stacks Project, Tag 0B6I, final proof paragraph
(blueprint: lem-pc-dq-coherator-adjunction).

Proof: a chain map from O_Y[-i] to I is an i-cocycle of global sections, and
homotopies correspond to i-coboundaries. Passage to the homotopy category gives
H^i(Γ(Y,I)). The K-injective comparison (`lem-sc-kinjective-quasi-iso-comparison`)
identifies these homotopy classes with morphisms in the derived category.
This identification is additive and natural in I. -/
theorem globalSections_homology_equiv_structureSheaf_shift (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [I.IsKInjective] (i : ℤ) :
    Nonempty
      (((((RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i) ≃+
        ((((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦-i⟧) ⟶
              DerivedCategory.Q.obj I)) := by
  let Γ := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let K := (Γ.mapHomologicalComplex (.up ℤ)).obj I
  let U := forget₂ (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤)))
    AddCommGrpCat
  let e := (HomologicalComplex.homologyFunctor _ _ i).mapIso
    (unitHomComplexSectionsIso Y I)
  let eH := e ≪≫ (K.sc i).mapHomologyIso U
  exact ⟨eH.addCommGroupIsoToAddEquiv.symm.trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ I i).trans (unitClassDerivedEquiv Y I i))⟩


/-- Any coherator right adjoint detects quasi-isomorphisms on derived global sections,
computed on K-injective representatives of the source and target.
Source: Stacks Project, Tag 0B6I, final proof paragraph
(blueprint: lem-pc-dq-coherator-adjunction).

Proof: global sections of a K-injective representative compute RΓ
(`def-pc-global-derived-rhom`). Degree-i cocycles are chain maps from O_Y[-i],
and coboundaries are null homotopies. The K-injective comparison
(`lem-sc-kinjective-quasi-iso-comparison`) identifies this cohomology with derived Hom.
The shift O_Y[-i] has quasi-coherent cohomology (`lemma-coherent-base-change-invertible-sheaves`).
Adjunction identifies these groups with Hom into DQ_Y. An isomorphism after DQ_Y
therefore gives an isomorphism on each global cohomology group, which is precisely
quasi-isomorphism of the global-sections complexes. -/
theorem dqCoherator_detects_globalSections (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (DQ_Y : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y)
    (adj : (schemeDerivedQCohProperty Y).ι ⊣ DQ_Y)
    (I J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J)
    [IsIso (DQ_Y.map (DerivedCategory.Q.map f))] :
    QuasiIso (((RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  let Γ := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let U := forget₂ (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤)))
    AddCommGrpCat
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((Γ.mapHomologicalComplex (.up ℤ)).map f) U).mp
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let S := ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦-i⟧
  let M : schemeDerivedQCohCategory Y :=
    ⟨S, structureSheaf_shift_is_derivedQCoh Y i⟩
  have hHom : Function.Bijective (fun a : S ⟶ DerivedCategory.Q.obj I ↦
      a ≫ DerivedCategory.Q.map f) := by
    let e := ((adj.homEquiv M (DerivedCategory.Q.obj I)).trans
      (Iso.homCongr (Iso.refl M) (asIso (DQ_Y.map (DerivedCategory.Q.map f))))).trans
        (adj.homEquiv M (DerivedCategory.Q.obj J)).symm
    have he : ∀ a, e a = a ≫ DerivedCategory.Q.map f := by
      intro a
      apply (adj.homEquiv M (DerivedCategory.Q.obj J)).injective
      simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, Iso.homCongr_apply,
        Iso.refl_inv, Category.id_comp, asIso_hom]
      exact (adj.homEquiv_naturality_right a (DerivedCategory.Q.map f)).symm
    simpa only [← he] using e.bijective
  let eI := unitClassDerivedEquiv Y I i
  let eJ := unitClassDerivedEquiv Y J i
  have hb : Function.Bijective (DQComparisonAux.postClass (S :=
      (CochainComplex.singleFunctor _ 0).obj
        (SheafOfModules.unit (moduleRings Y.toRingedSpace))) f i) := by
    constructor
    · intro a b h
      apply eI.injective
      apply hHom.injective
      simpa only [eI, eJ, unitClassDerivedEquiv_naturality] using congrArg eJ h
    · intro b
      obtain ⟨a, ha⟩ := hHom.surjective (eJ b)
      refine ⟨eI.symm a, eJ.injective ?_⟩
      rw [unitClassDerivedEquiv_naturality, AddEquiv.apply_symm_apply]
      exact ha
  let ep := AddEquiv.ofBijective (DQComparisonAux.postClass f i) hb
  let epIso : AddCommGrpCat.of _ ≅ AddCommGrpCat.of _ := ep.toAddCommGrpIso
  have : IsIso (AddCommGrpCat.ofHom (DQComparisonAux.postClass (S :=
      (CochainComplex.singleFunctor _ 0).obj
        (SheafOfModules.unit (moduleRings Y.toRingedSpace))) f i)) :=
    inferInstanceAs (IsIso epIso.hom)
  change IsIso (HomologicalComplex.homologyMap
    (((Γ ⋙ U).mapHomologicalComplex (.up ℤ)).map f) i)
  rw [← isIso_comp_left_iff (unitClassSectionsIso Y I i).hom,
    ← unitClassSectionsIso_naturality Y f i]
  infer_instance

end AlgebraicGeometry
