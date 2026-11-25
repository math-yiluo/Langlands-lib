/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # The fixed Ext-to-sections comparison on resolution cocycles

Source: Stacks Project, Tags 015E and 06XR; Mathlib's injective-resolution
Ext comparison and the explicit Hom-complex homology construction.
-/

@[expose] public section
universe u v u' v' uA
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex HomComplex
noncomputable section
namespace CategoryTheory

/-- The acyclic comparison of an injective resolution is its usual derived comparison.
Source: Stacks Project, Tags 015E and 06XR.
(blueprint: new-abelian-injective-acyclic-comparison)

Proof: Lift the identity to the chosen injective resolution. Naturality of the
usual injective comparison identifies its homology map with the comparison
between the two resolutions. The mapped lift is a quasi-isomorphism because
both resolutions have acyclic terms. Cancel its inverse homology map in the
acyclic-resolution constructor. -/
theorem acyclic_comparison_of_injective
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X : C} (I : InjectiveResolution X) (p : ℕ) :
    F.rightDerivedObjIsoOfResolution I.ι
      (fun n ↦ Functor.rightAcyclic_of_injective (I.cocomplex.X n)) p =
    I.isoRightDerivedObj F p := by
  let R := injectiveResolution X
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 X) R I.ι
  have hφ : I.ι ≫ φ = R.ι := by simp [φ]
  have h := I.isoRightDerivedObj_hom_naturality (𝟙 X) R φ
    (by simpa using congrArg (fun g ↦ g.f 0) hφ) F p
  simp only [Functor.map_id, Category.id_comp] at h
  have : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map φ) :=
    F.quasiIso_map_of_rightAcyclic_nat φ
      (fun n ↦ Functor.rightAcyclic_of_injective (I.cocomplex.X n))
      (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n))
  change (R.isoRightDerivedObj F p).hom =
    (I.isoRightDerivedObj F p).hom ≫ HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map φ) p at h
  apply Iso.ext
  change (R.isoRightDerivedObj F p).hom ≫
    (asIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map φ) p)).inv = _
  rw [h, Category.assoc]
  change (I.isoRightDerivedObj F p).hom ≫
    (asIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map φ) p)).hom ≫
    (asIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map φ) p)).inv = _
  rw [Iso.hom_inv_id, Category.comp_id]

/-- A chain map computes a map whenever both computations agree on cycle representatives.
The homology projection is surjective. Lift the chosen homology element, use
injectivity of the source comparison to recover its cohomology representative,
and apply naturality of the homology projection to the chain map.
Source: Mathlib, HomologicalComplex.homologyπ_naturality.
(blueprint: new-abelian-cycle-representative-transfer) -/
theorem homology_transfer_of_cycle_representatives
    {E E' : Type*} (K B : CochainComplex AddCommGrpCat.{u} ℕ) (t : K ⟶ B) (p : ℕ)
    (e : E → K.homology p) (he : Function.Injective e)
    (e' : E' → B.homology p) (g : E → E')
    (repr : K.cycles p → E)
    (hsource : ∀ z, e (repr z) = K.homologyπ p z)
    (htarget : ∀ z, e' (g (repr z)) =
      B.homologyπ p (HomologicalComplex.cyclesMap t p z)) (x : E) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map t) (e x) =
      e' (g x) := by
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ p)).mp inferInstance
    (e x)
  have hx : x = repr z := he (hz.symm.trans (hsource z).symm)
  rw [hx, hsource, htarget]
  change (HomologicalComplex.homologyMap t p) (K.homologyπ p z) = _
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t p) z

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
attribute [local irreducible] InjectiveResolution.isoRightDerivedObj
attribute [local irreducible] extRightDerivedHomObjIso sectionsIso

private theorem derived_nattrans_resolution
    {C : Type uA} [Category.{u} C] [Abelian C] [HasInjectiveResolutions C]
    (E G : C ⥤ AddCommGrpCat.{u}) [E.Additive] [G.Additive]
    (η : E ⟶ G) {Y : C} (I : InjectiveResolution Y) (p : ℕ) :
    (NatTrans.rightDerived η p).app Y ≫ (I.isoRightDerivedObj G p).hom =
    (I.isoRightDerivedObj E p).hom ≫ HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex η (.up ℕ)).app I.cocomplex) p := by
  rw [I.rightDerived_app_eq η p]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    HomologicalComplex.homologyFunctor_map]

private theorem site_sections_hom_formula
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) (p : ℕ) :
    (siteSectionsObjIso J U F p).hom =
    (extRightDerivedHomObjIso
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free))
      F p).hom ≫ (NatTrans.rightDerived (sectionsIso J U).hom p).app F := by
  rfl

private theorem standard_ext_hom_formula
    {A : Type uA} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    [HasInjectiveResolutions A] (P F : A) (p : ℕ) :
    let I := injectiveResolution F
    let E := preadditiveCoyoneda.obj (op P)
    (extRightDerivedHomObjIso P F p).hom ≫ (I.isoRightDerivedObj E p).hom =
    I.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
      (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj P)
        I.cochainComplex (p : ℤ)).homologyIso.inv ≫
      HomologicalComplex.homologyMap (extRightDerivedHomComplexIso P I.cochainComplex).hom
        (p : ℤ) ≫
      HomologicalComplex.homologyMap
        (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat E).hom (p : ℤ) ≫
      (((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat (rfl : (p : ℤ) = p)).hom := by
  dsimp only
  simp only [extRightDerivedHomObjIso,
    InjectiveResolution.isoRightDerivedObjCochainComplex,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, HomologicalComplex.homologyFunctor_map,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]


private theorem canonical_standard_ext_cocycle
    {C : Type uA} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    [HasInjectiveResolutions C] (A Y : C) (p : ℕ)
    (s : A ⟶ (injectiveResolution Y).cocomplex.X p)
    (hs : s ≫ (injectiveResolution Y).cocomplex.d p (p + 1) = 0)
    (c : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution Y).cocomplex).cycles p)
    (hc : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution Y).cocomplex).iCycles p c = s) :
    ((extRightDerivedHomObjIso A Y p).hom ≫
      ((injectiveResolution Y).isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) p).hom)
        ((injectiveResolution Y).extMk s (p + 1) rfl hs) =
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
        (injectiveResolution Y).cocomplex).homologyπ p c := by
  let I := injectiveResolution Y
  change s ≫ I.cocomplex.d p (p + 1) = 0 at hs
  let H := preadditiveCoyoneda.obj (op A)
  let e : H ≅ H := Iso.refl _
  let S := (singleFunctor C 0).obj A
  let K := (H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := HomComplex S I.cochainComplex
  let d := leftHomologyData S I.cochainComplex (p : ℤ)
  let k : L ≅ K.extend ComplexShape.embeddingUpNat :=
    extRightDerivedHomComplexIso A I.cochainComplex ≪≫
      I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat H
  let cI : AddCommGrpCat.of (Abelian.Ext A Y p) ≅
      AddCommGrpCat.of (CohomologyClass S I.cochainComplex (p : ℤ)) :=
    (I.extAddEquivCohomologyClass (X := A) (n := p)).toAddCommGrpIso
  let t := cI ≪≫ d.homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (p : ℤ)).mapIso k ≪≫
      K.extendHomologyIso ComplexShape.embeddingUpNat (j := p) rfl
  have heq : (extRightDerivedHomObjIso A Y p).hom ≫
      (I.isoRightDerivedObj H p).hom = t.hom := by
    simpa only [t, cI, k, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp,
      Category.assoc] using standard_ext_hom_formula A Y p
  rw [heq]
  let a : Cocycle S I.cochainComplex (p : ℤ) :=
    Cocycle.fromSingleMk (s ≫ (I.cochainComplexXIso p p rfl).inv) (zero_add _)
      (p + 1) (by lia) (by
        rw [I.cochainComplex_d _ _ p (p + 1) rfl (by simp)]
        simp [reassoc_of% hs])
  have ha : I.extAddEquivCohomologyClass (I.extMk s (p + 1) rfl hs) =
      CohomologyClass.mk a := by
    simp [a, InjectiveResolution.extAddEquivCohomologyClass_apply]
  let z : L.cycles (p : ℤ) := d.cyclesIso.inv a
  have hz : d.homologyIso.inv (CohomologyClass.mk a) = L.homologyπ (p : ℤ) z :=
    ConcreteCategory.congr_hom d.π_comp_homologyIso_inv a
  let w := HomologicalComplex.cyclesMap k.hom (p : ℤ) z
  let b : K.cycles p := (K.extendCyclesIso ComplexShape.embeddingUpNat rfl).hom w
  have hb : b = c := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles p)).1 inferInstance
    rw [hc]
    have hi₁ := ConcreteCategory.congr_hom
      (K.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat
        (j := p) (j' := (p : ℤ)) rfl) w
    have hi₂ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i k.hom (p : ℤ)) z
    simp only [ConcreteCategory.comp_apply] at hi₁ hi₂
    erw [hi₁, hi₂]
    have hz' : L.iCycles (p : ℤ) z = a.1 :=
      ConcreteCategory.congr_hom d.cyclesIso_inv_comp_iCycles a
    rw [hz']
    change (K.extendXIso ComplexShape.embeddingUpNat rfl).hom
      ((I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat H).hom.f (p : ℤ)
        (e.hom.app (I.cochainComplex.X (p : ℤ))
          (Cochain.fromSingleEquiv (zero_add (p : ℤ)) a.1))) = _
    dsimp only [a]
    erw [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
    have hk : (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat H).hom.f (p : ℤ) ≫
        (K.extendXIso ComplexShape.embeddingUpNat rfl).hom =
        H.map (I.cochainComplexXIso p p rfl).hom := by
      change (HomologicalComplex.mapExtendX I.cocomplex H
        (ComplexShape.embeddingUpNat.r (ComplexShape.embeddingUpNat.f p))).hom ≫ _ = _
      rw [HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f p)]
      simp [InjectiveResolution.cochainComplexXIso, HomologicalComplex.extendXIso,
        HomologicalComplex.extend.XIso, eqToHom_map]
    have hk' := ConcreteCategory.congr_hom hk
      (e.hom.app (I.cochainComplex.X (p : ℤ))
        (s ≫ (I.cochainComplexXIso p p rfl).inv))
    simp only [ConcreteCategory.comp_apply] at hk'
    erw [hk']
    have he := ConcreteCategory.congr_hom
      (e.hom.naturality (I.cochainComplexXIso p p rfl).hom)
      (show A ⟶ I.cochainComplex.X (p : ℤ) from
        s ≫ (I.cochainComplexXIso p p rfl).inv)
    change e.hom.app _ ((s ≫ (I.cochainComplexXIso p p rfl).inv) ≫
      (I.cochainComplexXIso p p rfl).hom) = _ at he
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ConcreteCategory.comp_apply] at he
    exact he.symm
  change (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
    (HomologicalComplex.homologyMap k.hom (p : ℤ)
      (d.homologyIso.inv (I.extAddEquivCohomologyClass (I.extMk s (p + 1) rfl hs)))) = _
  rw [ha, hz]
  have hp₁ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality k.hom (p : ℤ)) z
  have hp₂ := ConcreteCategory.congr_hom
    (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat
      (j := p) (j' := (p : ℤ)) rfl) w
  simp only [ConcreteCategory.comp_apply] at hp₁ hp₂
  erw [hp₁, hp₂]
  exact congrArg (K.homologyπ p) hb



private theorem canonical_ext_cocycle
    {C : Type uA} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    [HasInjectiveResolutions C] (A Y : C) (I : InjectiveResolution Y) (p : ℕ)
    (s : A ⟶ I.cocomplex.X p) (hs : s ≫ I.cocomplex.d p (p + 1) = 0)
    (c : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).cycles p)
    (hc : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).iCycles p c = s) :
    ((extRightDerivedHomObjIso A Y p).hom ≫
      (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) p).hom)
        (I.extMk s (p + 1) rfl hs) =
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homologyπ p c := by
  let q : AddCommGrpCat.of (Abelian.Ext A Y p) ⟶
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology p :=
    (extRightDerivedHomObjIso A Y p).hom ≫
      (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) p).hom
  change q (I.extMk s (p + 1) rfl hs) = _
  let E := preadditiveCoyoneda.obj (op A)
  let R := injectiveResolution Y
  let φ := InjectiveResolution.desc (𝟙 Y) R I
  have hφ : I.ι ≫ φ = R.ι := by simp [φ]
  have hφ₀ : I.ι.f 0 ≫ φ.f 0 = (𝟙 Y) ≫ R.ι.f 0 := by
    simpa using congrArg (fun g ↦ g.f 0) hφ
  let ψ := (E.mapHomologicalComplex (.up ℕ)).map φ
  let eI : (E.rightDerived p).obj Y ≅
      ((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p :=
    I.isoRightDerivedObj E p
  let eR : (E.rightDerived p).obj Y ≅
      ((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
    R.isoRightDerivedObj E p
  have hnat : eR.hom = eI.hom ≫ HomologicalComplex.homologyMap ψ p := by
    have h := I.isoRightDerivedObj_hom_naturality (𝟙 Y) R φ hφ₀ E p
    change (E.rightDerived p).map (𝟙 Y) ≫ eR.hom =
      eI.hom ≫ HomologicalComplex.homologyMap ψ p at h
    erw [(E.rightDerived p).map_id Y, Category.id_comp] at h
    exact h
  have hIso : IsIso (HomologicalComplex.homologyMap ψ p) := by
    have hh : eI.inv ≫ eR.hom = HomologicalComplex.homologyMap ψ p := by
      rw [hnat, Iso.inv_hom_id_assoc]
    rw [← hh]
    infer_instance
  apply (AddCommGrpCat.mono_iff_injective (HomologicalComplex.homologyMap ψ p)).1
    inferInstance
  have hsφ : (s ≫ φ.f p) ≫ R.cocomplex.d p (p + 1) = 0 := by
    simp [Category.assoc, φ.comm, reassoc_of% hs]
  have hcφ : (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).iCycles p)
      (HomologicalComplex.cyclesMap ψ p c) = s ≫ φ.f p := by
    have hh := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ p) c
    change (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).iCycles p)
      (HomologicalComplex.cyclesMap ψ p c) = (φ.f p |> E.map)
        ((((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles p) c) at hh
    change _ = s ≫ φ.f p
    rw [hc] at hh
    exact hh
  have hext : R.extMk (s ≫ φ.f p) (p + 1) rfl hsφ = I.extMk s (p + 1) rfl hs := by
    have hh := InjectiveResolution.extMk_comp_mk₀ s (p + 1) rfl hs
      (⟨φ, by simpa using hφ₀⟩ : I.Hom R (𝟙 Y))
    simpa using hh.symm
  have hr := canonical_standard_ext_cocycle A Y p (s ≫ φ.f p) hsφ
    (HomologicalComplex.cyclesMap ψ p c) hcφ
  let qR : AddCommGrpCat.of (Abelian.Ext A Y p) ⟶
      ((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
    (extRightDerivedHomObjIso A Y p).hom ≫ eR.hom
  have hq : q ≫ HomologicalComplex.homologyMap ψ p = qR := by
    change ((extRightDerivedHomObjIso A Y p).hom ≫ eI.hom) ≫
      HomologicalComplex.homologyMap ψ p = (extRightDerivedHomObjIso A Y p).hom ≫ eR.hom
    rw [Category.assoc, ← hnat]
  calc
    (HomologicalComplex.homologyMap ψ p) (q (I.extMk s (p + 1) rfl hs)) =
        qR (I.extMk s (p + 1) rfl hs) := ConcreteCategory.congr_hom hq _
    _ = qR (R.extMk (s ≫ φ.f p) (p + 1) rfl hsφ) := congrArg qR hext.symm
    _ = (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homologyπ p)
        (HomologicalComplex.cyclesMap ψ p c) := hr
    _ = _ := (ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality ψ p) c).symm


private theorem canonical_functor_iso_cocycle
    {C : Type uA} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    [HasInjectiveResolutions C] (A Y : C) (I : InjectiveResolution Y)
    (G : C ⥤ AddCommGrpCat.{u}) [G.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ G) (p : ℕ)
    (a : A ⟶ I.cocomplex.X p) (ha : a ≫ I.cocomplex.d p (p + 1) = 0)
    (c : ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).cycles p)
    (hc : ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles p c =
      e.hom.app (I.cocomplex.X p) a) :
    ((extRightDerivedHomObjIso A Y p).hom ≫
      (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) p).hom ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex e.hom (.up ℕ)).app I.cocomplex) p)
      (I.extMk a (p + 1) rfl ha) =
    ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ p c := by
  let E := preadditiveCoyoneda.obj (op A)
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let B := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let z : K.cycles p := (K.sc p).abCyclesIso.inv
    ⟨a, by
      change a ≫ I.cocomplex.d p ((ComplexShape.up ℕ).next p) = 0
      rw [CochainComplex.next ℕ p]
      exact ha⟩
  have hz : K.iCycles p z = a := (K.sc p).abCyclesIso_inv_apply_iCycles _
  let ψ := (NatTrans.mapHomologicalComplex e.hom (.up ℕ)).app I.cocomplex
  have hw : HomologicalComplex.cyclesMap ψ p z = c := by
    apply (AddCommGrpCat.mono_iff_injective (B.iCycles p)).1 inferInstance
    have hh := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ p) z
    simp only [ConcreteCategory.comp_apply] at hh
    rw [hh, hz, hc]
    rfl
  let qE : AddCommGrpCat.of (Abelian.Ext A Y p) ⟶ K.homology p :=
    (extRightDerivedHomObjIso A Y p).hom ≫ (I.isoRightDerivedObj E p).hom
  have he : qE (I.extMk a (p + 1) rfl ha) = K.homologyπ p z :=
    canonical_ext_cocycle A Y I p a ha z hz
  change ((extRightDerivedHomObjIso A Y p).hom ≫
    (I.isoRightDerivedObj E p).hom ≫ HomologicalComplex.homologyMap ψ p)
      (I.extMk a (p + 1) rfl ha) = _
  rw [← Category.assoc]
  change (HomologicalComplex.homologyMap ψ p) (qE (I.extMk a (p + 1) rfl ha)) = _
  rw [he]
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ψ p) z
  simpa only [ConcreteCategory.comp_apply, hw] using hh

private theorem canonical_derived_functor_iso_cocycle
    {C : Type uA} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    [HasInjectiveResolutions C] (A Y : C) (I : InjectiveResolution Y)
    (G : C ⥤ AddCommGrpCat.{u}) [G.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ G) (p : ℕ)
    (a : A ⟶ I.cocomplex.X p) (ha : a ≫ I.cocomplex.d p (p + 1) = 0)
    (c : ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).cycles p)
    (hc : ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles p c =
      e.hom.app (I.cocomplex.X p) a) :
    (((extRightDerivedHomObjIso A Y p).hom ≫ (NatTrans.rightDerived e.hom p).app Y) ≫
      (I.isoRightDerivedObj G p).hom) (I.extMk a (p + 1) rfl ha) =
    ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ p c := by
  rw [Category.assoc, derived_nattrans_resolution]
  exact canonical_functor_iso_cocycle A Y I G e p a ha c hc

attribute [local irreducible] siteSectionsObjIso
attribute [local irreducible] Functor.rightDerivedObjIsoOfResolution

/-- The prescribed site-sections comparison sends an Ext cocycle to its section class.
Source: Stacks Project, Tag 06XR; Mathlib, InjectiveResolution.extEquivCohomologyClass_extMk.
(blueprint: new-abelian-ext-sections-cocycle-normalization)

Proof: For the chosen resolution, unfold the fixed Ext/right-derived-Hom
constructor. Its derived-resolution factors cancel. The explicit Ext-to-Hom
cocycle comparison and the left homology data then send the cocycle to its
homology class. For an arbitrary injective resolution, compare with the chosen
one, use naturality, and cancel the homology map of the comparison. Transport
through the sections natural isomorphism, using right-derived naturality.
Finally use the defining formula for siteSectionsObjIso. This identifies the
actual prescribed map, in every degree, rather than choosing a new comparison. -/
theorem canonical_site_sections_cocycle
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (p : ℕ)
    (a : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X p)
    (ha : a ≫ I.cocomplex.d p (p + 1) = 0)
    (c : (((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).cycles p)
    (hc : (((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).iCycles p c = (sectionsIso J U).hom.app (I.cocomplex.X p) a) :
    ((siteSectionsObjIso J U F p).hom ≫
      (I.isoRightDerivedObj (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) p).hom)
      (I.extMk a (p + 1) rfl ha) =
    (((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homologyπ p c := by
  rw [site_sections_hom_formula]
  exact canonical_derived_functor_iso_cocycle _ F I _ (sectionsIso J U) p a ha c hc

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
