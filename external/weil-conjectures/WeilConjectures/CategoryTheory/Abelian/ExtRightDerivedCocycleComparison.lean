/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ConcreteCategory
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Normalization of the derived representable comparison on cocycles -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex in
private noncomputable def representedHomComplexIso
    {C : Type u} [Category.{v} C] [Abelian C] (A : C) (K : CochainComplex C ℤ) :
    HomComplex ((CochainComplex.singleFunctor C 0).obj A) K ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.fromSingleEquiv (zero_add n)).toAddCommGrpIso) (by
      intro i j hij
      ext a
      obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
      change (Cochain.fromSingleEquiv (zero_add i)
        (Cochain.fromSingleMk a (zero_add i)) ≫ K.d i j) =
        (Cochain.fromSingleEquiv (zero_add j)
          (δ i j (Cochain.fromSingleMk a (zero_add i))))
      simp only [Cochain.δ_fromSingleMk, zero_add, Cochain.fromSingleEquiv_fromSingleMk])

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex in
/-- The resolution-local Ext comparison takes a represented cocycle to its homology class.
Source: Stacks Project, Tag 06XR, Lemma 13.27.2 (injective resolution computation).

Proof: Identify Ext with cohomology classes in the Hom complex from single(A,0) to
I.cochainComplex by InjectiveResolution.extAddEquivCohomologyClass. The from-single
additive equivalence identifies this Hom complex with Hom(A,I.cochainComplex),
commuting with differentials by Cochain.δ_fromSingleMk. Apply e degreewise and
then take homology. Restriction from integer degrees to nonnegative degrees
identifies this homology with that of H(I.cocomplex), including degree zero
because the negative terms are zero. The formula extEquivCohomologyClass_extMk
identifies the Ext class with its from-single cocycle class. The image of its
cycle inclusion is e(s); monicity of iCycles identifies that cycle with c, so
its image is homologyπ(c). This is an objectwise statement about a supplied
resolution; it asserts neither naturality nor a comparison with rightDerived. -/
private theorem exists_ext_resolution_cocycle_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    (A : C) (H : C ⥤ AddCommGrpCat.{v}) [H.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ H)
    {Y : C} (I : InjectiveResolution Y) (p : ℕ) :
    ∃ t : ((Abelian.extFunctor p).obj (op A)).obj Y ≅
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology p,
      ∀ (s : A ⟶ I.cocomplex.X p) (hs : s ≫ I.cocomplex.d p (p + 1) = 0)
        (c : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles p)
        (hc : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles p c =
          e.hom.app (I.cocomplex.X p) s),
        t.hom (I.extMk s (p + 1) rfl hs) =
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ p c := by
  let S := (singleFunctor C 0).obj A
  let K := (H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := HomComplex S I.cochainComplex
  let d := leftHomologyData S I.cochainComplex (p : ℤ)
  let k : L ≅ K.extend ComplexShape.embeddingUpNat :=
    representedHomComplexIso A I.cochainComplex ≪≫
      (NatIso.mapHomologicalComplex e (.up ℤ)).app I.cochainComplex ≪≫
      I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat H
  let cI : AddCommGrpCat.of (Abelian.Ext A Y p) ≅
      AddCommGrpCat.of (CohomologyClass S I.cochainComplex (p : ℤ)) :=
    (I.extAddEquivCohomologyClass (X := A) (n := p)).toAddCommGrpIso
  let t := cI ≪≫ d.homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (p : ℤ)).mapIso k ≪≫
      K.extendHomologyIso ComplexShape.embeddingUpNat (j := p) rfl
  refine ⟨t, ?_⟩
  intro s hs c hc
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

private lemma resolution_comparison_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    (A : C) (H : C ⥤ AddCommGrpCat.{v}) [H.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ H)
    {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z)
    (f : Y ⟶ Z) (φ : I.Hom J f) (p : ℕ)
    (tI : ((Abelian.extFunctor p).obj (op A)).obj Y ≅
      ((H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p)
    (tJ : ((Abelian.extFunctor p).obj (op A)).obj Z ≅
      ((H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).homology p)
    (hI : ∀ s hs c, ((H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles p c =
      e.hom.app (I.cocomplex.X p) s → tI.hom (I.extMk s (p + 1) rfl hs) =
        ((H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ p c)
    (hJ : ∀ s hs c, ((H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).iCycles p c =
      e.hom.app (J.cocomplex.X p) s → tJ.hom (J.extMk s (p + 1) rfl hs) =
        ((H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).homologyπ p c) :
    ((Abelian.extFunctor p).obj (op A)).map f ≫ tJ.hom =
      tI.hom ≫ (H.mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ _ p).map φ.hom := by
  let : HasForget₂ AddCommGrpCat.{v} AddCommGrpCat.{v} := ⟨𝟭 _, rfl⟩
  let : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).Additive :=
    inferInstanceAs (𝟭 AddCommGrpCat.{v}).Additive
  let : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).PreservesHomology :=
    inferInstanceAs (𝟭 AddCommGrpCat.{v}).PreservesHomology
  ext a
  obtain ⟨s, hs, rfl⟩ := I.extMk_surjective a (p + 1) rfl
  let K := (H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let ψ := (H.mapHomologicalComplex (.up ℕ)).map φ.hom
  have hz : H.map (I.cocomplex.d p (p + 1)) (e.hom.app (I.cocomplex.X p) s) = 0 := by
    have h := ConcreteCategory.congr_hom (e.hom.naturality (I.cocomplex.d p (p + 1))) s
    change e.hom.app _ (s ≫ I.cocomplex.d p (p + 1)) =
      H.map _ (e.hom.app _ s) at h
    rw [← h, hs]
    exact map_zero _
  let c : K.cycles p := K.cyclesMk (e.hom.app (I.cocomplex.X p) s) (p + 1) (by simp) hz
  have hc : K.iCycles p c = e.hom.app (I.cocomplex.X p) s :=
    K.i_cyclesMk _ _ _ _
  have hc' : L.iCycles p (HomologicalComplex.cyclesMap ψ p c) =
      e.hom.app (J.cocomplex.X p) (s ≫ φ.hom.f p) := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ p) c
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hc] at h
    exact h.trans (ConcreteCategory.congr_hom (e.hom.naturality (φ.hom.f p)) s).symm
  change tJ.hom ((I.extMk s (p + 1) rfl hs).comp (Abelian.Ext.mk₀ f) (add_zero p)) =
    HomologicalComplex.homologyMap ψ p (tI.hom (I.extMk s (p + 1) rfl hs))
  rw [InjectiveResolution.extMk_comp_mk₀ s (p + 1) rfl hs φ, hJ _ _ _ hc', hI _ _ _ hc]
  exact (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ψ p) c).symm

set_option linter.unusedVariables false in
/-- A represented additive functor has an Ext comparison normalized on every resolution.

Source: Stacks Project, Derived Categories, Tag 06XR, Lemma 13.27.2;
Tag 013P, comparison maps between injective resolutions.
(blueprint: lem-sc-ext-right-derived-cocycle-comparison)

Proof: For the chosen injective resolution of Y, identify Ext from A with cohomology
classes of Hom(single(A,0),I) using extAddEquivCohomologyClass. The from-single
additive equivalence identifies that Hom complex with Hom(A,I) degreewise, commuting
with differentials. Apply the given natural isomorphism e degreewise and take homology;
compose with the inverse of isoRightDerivedObj. This defines the inverse component
of x. For a coefficient map, lift it between injective resolutions. Postcomposition
commutes with the from-single equivalence and e; extMk_comp_mk₀ identifies the map
on Ext classes, and isoRightDerivedObj_naturality identifies the derived map.
Thus these components assemble into a natural isomorphism. For another resolution,
use a comparison lifting the identity: the same naturality calculation, together
with homotopy independence, identifies its computation with the chosen one.
The identity extEquivCohomologyClass_extMk says that the class of s is the class of
its from-single cocycle. Its image under the complex isomorphism has underlying
cycle e(s). Since iCycles is monic, it is precisely c when hc holds, and the homology
class is homologyπ(c). This proves the displayed normalization for every I.
The argument includes degree zero, the zero object, and arbitrary zero cocycles;
no projectivity of A or exactness of H is used. -/
theorem exists_ext_rightDerived_cocycle_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    [HasInjectiveResolutions C] (A : C) (H : C ⥤ AddCommGrpCat.{v}) [H.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ H) :
    ∃ x : ∀ n : ℕ, H.rightDerived n ≅ (Abelian.extFunctor n).obj (op A),
      ∀ (Y : C) (I : InjectiveResolution Y) (p : ℕ)
        (s : A ⟶ I.cocomplex.X p) (hs : s ≫ I.cocomplex.d p (p + 1) = 0)
        (c : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles p)
        (hc : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles p c =
          e.hom.app (I.cocomplex.X p) s),
        (I.isoRightDerivedObj H p).hom ((x p).inv.app Y (I.extMk s (p + 1) rfl hs)) =
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ p c := by
  classical
  choose t ht using fun (Y : C) (I : InjectiveResolution Y) (p : ℕ) ↦
    exists_ext_resolution_cocycle_iso A H e I p
  let b := fun (Y : C) (I : InjectiveResolution Y) (p : ℕ) ↦
    t Y I p ≪≫ (I.isoRightDerivedObj H p).symm
  have hb : ∀ {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z)
      (f : Y ⟶ Z) (φ : I.Hom J f) (p : ℕ),
      ((Abelian.extFunctor p).obj (op A)).map f ≫ (b Z J p).hom =
        (b Y I p).hom ≫ (H.rightDerived p).map f := by
    intro Y Z I J f φ p
    dsimp only [b, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, resolution_comparison_naturality A H e I J f φ p
      (t Y I p) (t Z J p) (ht Y I p) (ht Z J p), Category.assoc,
      Category.assoc, ← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ.hom
        (by simpa only [CochainComplex.single₀_map_f_zero] using
          φ.ι_f_zero_comp_hom_f_zero) H p]
  let x : ∀ p : ℕ, H.rightDerived p ≅ (Abelian.extFunctor p).obj (op A) := fun p ↦
    (NatIso.ofComponents (fun Y ↦ b Y (injectiveResolution Y) p) (by
      intro Y Z f
      exact hb (injectiveResolution Y) (injectiveResolution Z) f
        ⟨InjectiveResolution.desc f _ _, by simp⟩ p)).symm
  refine ⟨x, ?_⟩
  intro Y I p s hs c hc
  let φ : (injectiveResolution Y).Hom I (𝟙 Y) :=
    ⟨InjectiveResolution.desc (𝟙 Y) I (injectiveResolution Y), by simp⟩
  have hi := hb (injectiveResolution Y) I (𝟙 Y) φ p
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at hi
  have he : (x p).inv.app Y = (b Y I p).hom := hi.symm
  rw [he]
  change (I.isoRightDerivedObj H p).hom
    ((I.isoRightDerivedObj H p).inv ((t Y I p).hom (I.extMk s (p + 1) rfl hs))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  exact ht Y I p s hs c hc

end CategoryTheory
