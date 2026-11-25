/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Object cohomology equivalences normalized on cocycles

Source: Stacks Project, Section 01FT and Tag 06XR (1).
(blueprint: lem-weil-pbc-object-resolution-cocycle-equivalence)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

/-- The section complex of a complex of abelian sheaves. -/
abbrev sheafSectionComplex
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (V : C) :=
  ((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)).mapHomologicalComplex
      (.up ℕ)).obj K

/-- Evaluate a morphism from the free representable sheaf at the identity generator. -/
noncomputable def sheafCocycleSection
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q) : (sheafSectionComplex J K V).X q :=
  (a.hom.app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V)))

/-- A sheaf cocycle evaluates to a section cocycle. -/
theorem sheafCocycleSection_closed
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q)
    (ha : a ≫ K.d q (q + 1) = 0) :
    ((sheafSectionComplex J K V).d q (q + 1)).hom
      (sheafCocycleSection J K q V a) = 0 := by
  have h := congrArg (fun f ↦ (f.hom.app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V)))) ha
  exact h

/-- A cycle in degree q belongs to the kernel used by the short-complex homology API. -/
theorem sectionCycle_mem_kernel (K : CochainComplex AddCommGrpCat.{v} ℕ)
    (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0) :
    x ∈ (K.sc q).g.hom.ker := by
  change (K.d q ((ComplexShape.up ℕ).next q)).hom x = 0
  rw [CochainComplex.next ℕ q]
  exact hx

/-- The homology class of a cycle in a complex of abelian groups. -/
noncomputable def sectionCycleClass (K : CochainComplex AddCommGrpCat.{v} ℕ)
    (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0) : K.homology q :=
  (K.homologyπ q).hom ((K.sc q).abCyclesIso.inv
    ⟨x, sectionCycle_mem_kernel K q x hx⟩)

/-- The homology class of a section cocycle, constructed from the actual section. -/
noncomputable def sheafCocycleSectionClass
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q)
    (ha : a ≫ K.d q (q + 1) = 0) : (sheafSectionComplex J K V).homology q :=
  sectionCycleClass (sheafSectionComplex J K V) q (sheafCocycleSection J K q V a)
    (sheafCocycleSection_closed J K q V a ha)

/-- The nonnegative complex of maps from X into K. -/
private abbrev nonnegativeHomComplex
    {A : Type u} [Category.{v} A] [Preadditive A]
    (X : A) (K : CochainComplex A ℕ) :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj K

private theorem extMk_zero_degree_iff
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {X F : A} (I : InjectiveResolution F) (a : X ⟶ I.cocomplex.X 0)
    (ha : a ≫ I.cocomplex.d 0 1 = 0) :
    I.extMk a 1 rfl ha = 0 ↔ a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    rw [← I.extEquivCohomologyClass.apply_eq_iff_eq,
      I.extEquivCohomologyClass_extMk, I.extEquivCohomologyClass_zero,
      CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
    rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
      _ _ _ _ _ (-1) (by norm_num)]
    have hz := CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by norm_num)
    constructor
    · rintro ⟨g, hg⟩
      have hgz : g = 0 := hz.eq_of_tgt _ _
      rw [hgz, zero_comp] at hg
      exact (cancel_mono (I.cochainComplexXIso 0 0 rfl).inv).mp (by simpa using hg.symm)
    · rintro rfl
      exact ⟨0, by simp⟩

private theorem homCycle_closed
    {A : Type u} [Category.{v} A] [Preadditive A]
    (X : A) (K : CochainComplex A ℕ) (q : ℕ)
    (a : ((nonnegativeHomComplex X K).sc q).g.hom.ker) :
    a.val ≫ K.d q (q + 1) = 0 := by
  have ha := a.property
  change a.val ≫ K.d q ((ComplexShape.up ℕ).next q) = 0 at ha
  rwa [CochainComplex.next ℕ q] at ha

private noncomputable def homCyclesToExt
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    ((nonnegativeHomComplex X I.cocomplex).sc q).g.hom.ker →+ Abelian.Ext X F q where
  toFun a := I.extMk a.val (q + 1) rfl (homCycle_closed X I.cocomplex q a)
  map_zero' := I.extMk_zero _ _
  map_add' a b := (I.add_extMk a.val b.val _ _ _ _).symm

private theorem homCyclesToExt_surjective
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    Function.Surjective (homCyclesToExt X F I q) := by
  intro x
  obtain ⟨a, ha, h⟩ := I.extMk_surjective x (q + 1) rfl
  refine ⟨⟨a, ?_⟩, h⟩
  change a ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
  rwa [CochainComplex.next ℕ q]

private theorem homCyclesToExt_kernel
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    ((nonnegativeHomComplex X I.cocomplex).sc q).abToCycles.range =
      (homCyclesToExt X F I q).ker := by
  ext a
  change (∃ b, ((nonnegativeHomComplex X I.cocomplex).sc q).abToCycles b = a) ↔
    I.extMk a.val (q + 1) rfl (homCycle_closed X I.cocomplex q a) = 0
  simp only [Subtype.ext_iff]
  change (∃ b : X ⟶ I.cocomplex.X ((ComplexShape.up ℕ).prev q),
    b ≫ I.cocomplex.d ((ComplexShape.up ℕ).prev q) q = a.val) ↔ _
  cases q with
  | zero =>
    rw [CochainComplex.prev_nat_zero, extMk_zero_degree_iff]
    have hd : I.cocomplex.d 0 0 = 0 := I.cocomplex.shape _ _ (by simp)
    erw [hd]
    simp only [comp_zero]
    exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨0, h.symm⟩⟩
  | succ p =>
    rw [CochainComplex.prev_nat_succ, I.extMk_eq_zero_iff _ _ _ _ p rfl]

private theorem injectiveResolution_homology_cocycle
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    ∃ (e : Abelian.Ext X F q ≃+ (nonnegativeHomComplex X I.cocomplex).homology q),
      ∀ (a : X ⟶ I.cocomplex.X q) (ha : a ≫ I.cocomplex.d q (q + 1) = 0),
        e (I.extMk a (q + 1) rfl ha) =
          ((nonnegativeHomComplex X I.cocomplex).homologyπ q).hom
            (((nonnegativeHomComplex X I.cocomplex).sc q).abCyclesIso.inv
              ⟨a, by
                change a ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
                rw [CochainComplex.next ℕ q]
                exact ha⟩) := by
  set_option backward.isDefEq.respectTransparency false in
    let K := nonnegativeHomComplex X I.cocomplex
    let S := K.sc q
    let t := QuotientAddGroup.liftEquiv S.abToCycles.range
      (homCyclesToExt_surjective X F I q) (homCyclesToExt_kernel X F I q)
    let d := S.abHomologyIso.addCommGroupIsoToAddEquiv
    refine ⟨t.symm.trans d.symm, ?_⟩
    intro a ha
    let z : S.g.hom.ker := ⟨a, by
      change a ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
      rwa [CochainComplex.next ℕ q]⟩
    apply (t.symm.trans d.symm).symm.injective
    erw [AddEquiv.symm_apply_apply]
    change I.extMk a (q + 1) rfl ha =
      t (S.abHomologyIso.hom (K.homologyπ q (S.abCyclesIso.inv z)))
    change _ = t (((S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom).hom) z)
    change _ = t (((S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
      S.abLeftHomologyData.homologyIso.hom).hom) z)
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl


private noncomputable def representableSectionsEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (V : C) (A : Sheaf J AddCommGrpCat.{v}) :
    ((presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) ≃+ A.obj.obj (op V) := by
  let e := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ A).trans
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj V) A.obj).trans
      yonedaEquiv)
  refine { toEquiv := e, map_add' := ?_ }
  intro a b
  dsimp [e, Adjunction.homEquiv, yonedaEquiv]

private theorem representableSectionsEquiv_apply
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q) :
    representableSectionsEquiv J V (K.X q) a = sheafCocycleSection J K q V a := by
  rfl

private theorem representableSectionsEquiv_postcomp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (V : C)
    {A B : Sheaf J AddCommGrpCat.{v}} (f : A ⟶ B)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) :
    representableSectionsEquiv J V B (a ≫ f) =
      f.hom.app (op V) (representableSectionsEquiv J V A a) := by
  change yonedaEquiv
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj V) B.obj)
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ B) (a ≫ f))) =
    f.hom.app (op V) (yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj V) A.obj)
        (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ A) a)))
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def representableSectionComplexIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (V : C) :
    nonnegativeHomComplex ((presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free)) K ≅
      ((AddCommGrpCat.uliftFunctor.{u, v}).mapHomologicalComplex (.up ℕ)).obj
        (sheafSectionComplex J K V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ ((representableSectionsEquiv J V (K.X q)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) (by
      intro i j _
      ext a
      exact congrArg ULift.up (representableSectionsEquiv_postcomp J V (K.d i j) a).symm)

private theorem sectionCycleClass_map
    {K L : CochainComplex AddCommGrpCat.{v} ℕ}
    (f : K ⟶ L) (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0)
    (y : L.X q) (hy : (L.d q (q + 1)).hom y = 0) (h : (f.f q).hom x = y) :
    (HomologicalComplex.homologyMap f q).hom (sectionCycleClass K q x hx) =
      sectionCycleClass L q y hy := by
  set_option backward.isDefEq.respectTransparency false in
    let zx := (K.sc q).abCyclesIso.inv ⟨x, sectionCycle_mem_kernel K q x hx⟩
    let zy := (L.sc q).abCyclesIso.inv ⟨y, sectionCycle_mem_kernel L q y hy⟩
    have hz : (HomologicalComplex.cyclesMap f q).hom zx = zy := by
      apply (AddCommGrpCat.mono_iff_injective (L.iCycles q)).mp inferInstance
      change ((HomologicalComplex.cyclesMap f q) ≫ L.iCycles q) zx = (L.iCycles q) zy
      rw [HomologicalComplex.cyclesMap_i]
      change (f.f q) ((K.iCycles q) zx) = (L.iCycles q) zy
      dsimp only [zx, zy, HomologicalComplex.iCycles]
      erw [(K.sc q).abCyclesIso_inv_apply_iCycles,
        (L.sc q).abCyclesIso_inv_apply_iCycles]
      exact h
    change ((K.homologyπ q) ≫ HomologicalComplex.homologyMap f q) zx =
      (L.homologyπ q) zy
    rw [HomologicalComplex.homologyπ_naturality]
    change (L.homologyπ q) ((HomologicalComplex.cyclesMap f q) zx) = _
    rw [hz]

private theorem sectionCycleClass_ulift
    (K : CochainComplex AddCommGrpCat.{v} ℕ) (q : ℕ)
    (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0) :
    let U := AddCommGrpCat.uliftFunctor.{u, v}
    let L := (U.mapHomologicalComplex (.up ℕ)).obj K
    ((K.sc q).mapHomologyIso U).hom
      (sectionCycleClass L q (ULift.up x) (congrArg ULift.up hx)) =
        ULift.up (sectionCycleClass K q x hx) := by
  set_option backward.isDefEq.respectTransparency false in
    let U := AddCommGrpCat.uliftFunctor.{u, v}
    let L := (U.mapHomologicalComplex (.up ℕ)).obj K
    let zx := (K.sc q).abCyclesIso.inv ⟨x, sectionCycle_mem_kernel K q x hx⟩
    let zy := (L.sc q).abCyclesIso.inv
      ⟨ULift.up x, sectionCycle_mem_kernel L q (ULift.up x) (congrArg ULift.up hx)⟩
    have hz : ((K.sc q).leftHomologyData.map U).cyclesIso.hom zy = ULift.up zx := by
      apply (AddCommGrpCat.mono_iff_injective (U.map (K.iCycles q))).mp inferInstance
      change (((K.sc q).leftHomologyData.map U).cyclesIso.hom ≫ U.map (K.iCycles q)) zy = _
      change ((((K.sc q).leftHomologyData.map U).cyclesIso.hom ≫
        ((K.sc q).leftHomologyData.map U).i).hom) zy = _
      rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
      change (L.iCycles q) zy = ULift.up ((K.iCycles q) zx)
      dsimp only [zx, zy, HomologicalComplex.iCycles]
      erw [(L.sc q).abCyclesIso_inv_apply_iCycles,
        (K.sc q).abCyclesIso_inv_apply_iCycles]
    change (((L.sc q).homologyπ ≫ ((K.sc q).mapHomologyIso U).hom).hom) zy =
      ULift.up ((K.homologyπ q) zx)
    rw [(K.sc q).leftHomologyData.mapHomologyIso_eq U]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
    change (U.map (K.sc q).leftHomologyData.homologyIso.inv)
      ((U.map (K.sc q).leftHomologyData.π)
        (((K.sc q).leftHomologyData.map U).cyclesIso.hom zy)) = _
    rw [hz]
    change ULift.up ((((K.sc q).leftHomologyData.π ≫
      (K.sc q).leftHomologyData.homologyIso.inv).hom) zx) = _
    rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
    have hi : (K.sc q).leftHomologyData.cyclesIso.inv zx = zx := by
      apply (AddCommGrpCat.mono_iff_injective (K.sc q).iCycles).mp inferInstance
      change (((K.sc q).leftHomologyData.cyclesIso.inv ≫ (K.sc q).iCycles).hom)
        zx = _
      rw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles]
      rfl
    exact congrArg (fun z ↦ ULift.up ((K.sc q).homologyπ z)) hi

/-- Object cohomology admits an equivalence carrying every Ext cocycle to its section class.

Source: Stacks Project, Section 01FT, equation-cohomology-object-site;
Tag 06XR (1), lemma-compute-ext-resolutions.
(blueprint: lem-weil-pbc-object-resolution-cocycle-equivalence)

Proof: Put P(V) equal to the sheafification of the free abelian presheaf on yoneda(V).
The sheafification adjunction, the free abelian adjunction, and Yoneda identify
Hom(P(V), A) additively with A(V), by evaluation at the image of the identity generator.
Naturality in A identifies the Hom cochain complex from P(V) to I with the section
complex of I. Compute Ext with the supplied injective resolution using
InjectiveResolution.extAddEquivCohomologyClass. Its formula on extMk identifies
extMk(a) with the class of a. Pass through the degreewise evaluation identification
and its homology isomorphism: this sends that class to sheafCocycleSectionClass(a).
For the integer extension of I, terms in negative degrees are zero, so restriction
to nonnegative degrees preserves degree-q homology, including q=0. If the Ext
universe differs from the sheaf morphism universe, first apply the canonical Ext
universe equivalence, whose formula on extMk preserves this calculation. The
composite is additive and invertible and gives the stated equivalence and formula.
Empty sites (no V), zero sheaves, and degree zero require no extra hypotheses. -/
theorem objectCohomology_resolution_cocycle_equivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (I : InjectiveResolution F) (q : ℕ) (V : C) :
    ∃ (e : Sheaf.H' F q V ≃+ (sheafSectionComplex J I.cocomplex V).homology q),
      ∀ (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q)
        (ha : a ≫ I.cocomplex.d q (q + 1) = 0),
        e (I.extMk a (q + 1) rfl ha) =
          sheafCocycleSectionClass J I.cocomplex q V a ha := by
  set_option backward.isDefEq.respectTransparency false in
    let P := (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free)
    obtain ⟨e, he⟩ := injectiveResolution_homology_cocycle P F I q
    let K := sheafSectionComplex J I.cocomplex V
    let U := AddCommGrpCat.uliftFunctor.{u, v}
    let c := representableSectionComplexIso J I.cocomplex V
    let h := (HomologicalComplex.homologyFunctor _ _ q).mapIso c
    let d := (K.sc q).mapHomologyIso U
    refine ⟨((e.trans h.addCommGroupIsoToAddEquiv).trans
      d.addCommGroupIsoToAddEquiv).trans AddEquiv.ulift, ?_⟩
    intro a ha
    change ULift.down (d.hom (h.hom (e (I.extMk a (q + 1) rfl ha)))) = _
    erw [he a ha]
    have hc := sectionCycleClass_map c.hom q a ha
      (ULift.up (sheafCocycleSection J I.cocomplex q V a))
      (congrArg ULift.up (sheafCocycleSection_closed J I.cocomplex q V a ha))
      (congrArg ULift.up (representableSectionsEquiv_apply J I.cocomplex q V a))
    change ULift.down (d.hom ((HomologicalComplex.homologyMap c.hom q).hom
      (sectionCycleClass _ q a ha))) = _
    rw [hc]
    exact congrArg ULift.down
      (sectionCycleClass_ulift K q (sheafCocycleSection J I.cocomplex q V a)
        (sheafCocycleSection_closed J I.cocomplex q V a ha))
