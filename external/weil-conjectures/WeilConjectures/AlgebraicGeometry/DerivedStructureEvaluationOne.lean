/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # The canonical global cohomology class of one

Source: Stacks Project, Tags 079V and 09M1.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section

-- Lift chain maps and homotopies componentwise using the same inverse on each Hom set.
set_option backward.isDefEq.respectTransparency false in
private theorem map_homotopy_bijective
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {ι : Type*} {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
    (K : HomologicalComplex C c)
    (h : ∀ i (Y : C), Function.Bijective
      (F.map : (K.X i ⟶ Y) → (F.obj (K.X i) ⟶ F.obj Y)))
    (L : HomologicalComplex C c) :
    Function.Bijective ((F.mapHomotopyCategory c).map :
      ((HomotopyCategory.quotient C c).obj K ⟶
        (HomotopyCategory.quotient C c).obj L) →
      ((F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj K) ⟶
        (F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj L))) := by
  classical
  let e (i : ι) (Y : C) := Equiv.ofBijective _ (h i Y)
  have he (i : ι) (Y : C) (f : F.obj (K.X i) ⟶ F.obj Y) :
      F.map ((e i Y).symm f) = f := (e i Y).apply_symm_apply f
  constructor
  · intro f g hfg
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective g
    let H := HomotopyCategory.homotopyOfEq _ _ hfg
    apply HomotopyCategory.eq_of_homotopy
    refine { hom := fun i j => (e i (L.X j)).symm (H.hom i j)
             zero := ?_, comm := ?_ }
    · intro i j hij
      apply (h i (L.X j)).1
      simp only [he, Functor.map_zero]
      exact H.zero i j hij
    · intro i
      apply (h i (L.X i)).1
      simpa [dNext, prevD, he, HomotopyCategory.quotient_obj_as] using H.comm i
  · intro f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient D c).map_surjective f
    let g : K ⟶ L :=
      { f := fun i => (e i (L.X i)).symm (f.f i)
        comm' := fun i j _ => by
          apply (h i (L.X j)).1
          simpa [he, HomotopyCategory.quotient_obj_as] using f.comm i j }
    refine ⟨(HomotopyCategory.quotient C c).map g, ?_⟩
    rw [Functor.mapHomotopyCategory_map]
    congr 1
    ext i
    exact he i (L.X i) (f.f i)

-- A map out of the unit is determined by one on the total open; restrict it to each open.
set_option backward.isDefEq.respectTransparency false in
private theorem unit_evaluation_bijective (X : RingedSpace.{u})
    (M : SheafOfModules.{u} (moduleRings X)) :
    Function.Bijective ((RingedSpace.globalSectionsFunctor X).map :
      (SheafOfModules.unit (moduleRings X) ⟶ M) →
      ((RingedSpace.globalSectionsFunctor X).obj (SheafOfModules.unit (moduleRings X)) ⟶
        (RingedSpace.globalSectionsFunctor X).obj M)) := by
  constructor
  · intro f g hfg
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    let i : op (⊤ : TopologicalSpace.Opens X) ⟶ U := (homOfLE le_top).op
    have hf := PresheafOfModules.naturality_apply f.val i (1 : (moduleRings X).obj.obj (op ⊤))
    have hg := PresheafOfModules.naturality_apply g.val i (1 : (moduleRings X).obj.obj (op ⊤))
    simp only [SheafOfModules.unit, PresheafOfModules.unit_map_one] at hf hg
    change f.val.app U (1 : (moduleRings X).obj.obj U) =
      g.val.app U (1 : (moduleRings X).obj.obj U)
    exact hf.trans ((congrArg (fun z => M.val.map i z)
      (CategoryTheory.congr_fun hfg (1 : (moduleRings X).obj.obj (op ⊤)))).trans hg.symm)
  · intro f
    let s : M.sections := M.val.sectionsMk
      (fun U => M.val.map ((homOfLE le_top).op) (f (1 : (moduleRings X).obj.obj (op ⊤)))) (by
        intro U V i
        rw [← PresheafOfModules.map_comp_apply]
        congr 1)
    refine ⟨M.unitHomEquiv.symm s, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (M.unitHomEquiv (M.unitHomEquiv.symm s)).val (op ⊤) =
      f (1 : (moduleRings X).obj.obj (op ⊤))
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 (op ⊤)) (f (1 : (moduleRings X).obj.obj (op ⊤))) =
      f (1 : (moduleRings X).obj.obj (op ⊤))
    simp

-- Transport the degree-zero bijection along the single-complex component isomorphism.
private theorem map_bijective_of_source_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {S U : C} (e : S ≅ U)
    (h : ∀ Y : C, Function.Bijective (F.map : (U ⟶ Y) → (F.obj U ⟶ F.obj Y)))
    (Y : C) : Function.Bijective (F.map : (S ⟶ Y) → (F.obj S ⟶ F.obj Y)) := by
  constructor
  · intro f g hfg
    have he : e.inv ≫ f = e.inv ≫ g := (h Y).1 (by simp [hfg])
    simpa using congrArg (fun k => e.hom ≫ k) he
  · intro f
    obtain ⟨g, hg⟩ := (h Y).2 (F.map e.inv ≫ f)
    refine ⟨e.hom ≫ g, ?_⟩
    simp [hg]


private theorem projective_single_to_negative_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (E : DerivedCategory C) [E.IsLE (-1)]
    (f : (DerivedCategory.singleFunctor C 0).obj P ⟶ E) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E (-1)
  let := hK
  have h : f ≫ e.hom = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (f ≫ e.hom) (-1) (by omega)
  simpa using (cancel_mono e.hom).1 (by simpa using h)

set_option backward.isDefEq.respectTransparency false in
private theorem projective_single_homology_bijective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (E : DerivedCategory C) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor C 0).obj P ⟶ E ↦
      (DerivedCategory.homologyFunctor C 0).map f) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let S := (DerivedCategory.singleFunctor C 0).obj P
  let T := (t.triangleLTGE 0).obj E
  have hT := t.triangleLTGE_distinguished 0 E
  have : t.IsLE T.obj₁ (-1) := by
    change t.IsLE ((t.truncLT 0).obj E) (0 - 1)
    infer_instance
  have hv (f : S ⟶ T.obj₁) : f = 0 := projective_single_to_negative_eq_zero P _ f
  have hv' (f : S ⟶ T.obj₁⟦(1 : ℤ)⟧) : f = 0 := by
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) := by
      have : t.IsLE T.obj₁ (-1) := inferInstance
      have := t.isLE_shift T.obj₁ (-1) 1 (-2) (by omega)
      exact t.isLE_of_le _ (-2) (-1) (by omega)
    exact projective_single_to_negative_eq_zero P _ f
  have hpost : Function.Bijective (fun f : S ⟶ E ↦ f ≫ T.mor₂) := by
    constructor
    · intro f g h
      obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT (f - g) (by simp [h])
      rw [hv a, Limits.zero_comp] at ha
      exact sub_eq_zero.mp ha
    · intro g
      obtain ⟨f, hf⟩ := T.coyoneda_exact₃ hT g (hv' (g ≫ T.mor₃))
      exact ⟨f, hf.symm⟩
  let H := DerivedCategory.homologyFunctor C 0
  have hH : Function.Bijective (fun f : S ⟶ T.obj₃ ↦ H.map f) :=
    DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0
  have hπ : IsIso (H.map T.mor₂) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E 0 0 le_rfl
  constructor
  · intro f g h
    apply hpost.1
    apply hH.1
    simpa only [Functor.map_comp] using
      congrArg (fun a ↦ a ≫ H.map T.mor₂) h
  · intro g
    obtain ⟨a, ha⟩ := hH.2 (g ≫ H.map T.mor₂)
    obtain ⟨f, hf⟩ := hpost.2 a
    refine ⟨f, (cancel_mono (H.map T.mor₂)).1 ?_⟩
    change f ≫ T.mor₂ = a at hf
    change H.map a = g ≫ H.map T.mor₂ at ha
    rw [← H.map_comp, hf, ha]



private theorem free_evaluation_bijective (A : Type u) [Ring A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (S E : DerivedCategory (ModuleCat.{u} A))
    (s : S ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    (ε : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj S ≅ ModuleCat.of A A) :
    Function.Bijective (fun f : S ⟶ E ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map f (ε.inv (1 : A))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  have h := projective_single_homology_bijective (ModuleCat.of A A) E
  have hH : Function.Bijective (H.map : (S ⟶ E) → (H.obj S ⟶ H.obj E)) := by
    constructor
    · intro f g hfg
      have hh : s.inv ≫ f = s.inv ≫ g := h.1 (by
        change H.map (s.inv ≫ f) = H.map (s.inv ≫ g)
        rw [H.map_comp, H.map_comp, hfg])
      exact (cancel_epi s.inv).1 hh
    · intro f
      obtain ⟨g, hg⟩ := h.2 (H.map s.inv ≫ f)
      change H.map g = H.map s.inv ≫ f at hg
      refine ⟨s.hom ≫ g, ?_⟩
      rw [H.map_comp, hg, ← Category.assoc, ← H.map_comp,
        s.hom_inv_id, H.map_id, Category.id_comp]
  let e : (H.obj S ⟶ H.obj E) ≃ H.obj E :=
    (Iso.homCongr ε (Iso.refl _)).trans
      (ModuleCat.homAddEquiv.trans
        (LinearMap.ringLmapEquivSelf A ℤ (H.obj E)).toAddEquiv).toEquiv
  have he := e.bijective.comp hH
  have heval (f : S ⟶ E) : e (H.map f) = H.map f (ε.inv (1 : A)) := by
    change (ε.inv ≫ H.map f ≫ 𝟙 _) (1 : A) = _
    rw [Category.comp_id]
    rfl
  simpa only [Function.comp_def, heval] using he

private theorem global_homotopy_map_bijective (X : RingedSpace.{u})
    (J : HomotopyCategory (SheafOfModules.{u} (moduleRings X)) (.up ℤ)) :
    let F := RingedSpace.globalSectionsFunctor X
    let P := (CochainComplex.singleFunctor (SheafOfModules.{u} (moduleRings X)) 0).obj
      (SheafOfModules.unit (moduleRings X))
    Function.Bijective ((F.mapHomotopyCategory (.up ℤ)).map :
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P ⟶ J) →
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⟶
        (F.mapHomotopyCategory (.up ℤ)).obj J)) := by
  let C := SheafOfModules.{u} (moduleRings X)
  let U := SheafOfModules.unit (moduleRings X)
  let F := RingedSpace.globalSectionsFunctor X
  let K := (CochainComplex.singleFunctor C 0).obj U
  have hK (i : ℤ) (Y : C) : Function.Bijective
      (F.map : (K.X i ⟶ Y) → (F.obj (K.X i) ⟶ F.obj Y)) := by
    by_cases hi : i = 0
    · subst i
      exact map_bijective_of_source_iso F
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 U)
        (unit_evaluation_bijective X) Y
    · have hz : IsZero (K.X i) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U i hi
      have hzF := F.map_isZero hz
      refine ⟨fun f g _ ↦ hz.eq_of_src f g, fun f ↦ ⟨0, ?_⟩⟩
      exact hzF.eq_of_src _ _
  exact map_homotopy_bijective F K hK J.as

private theorem evaluation_bijective_of_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (L : C ⥤ C') (M : D ⥤ D') (G : C ⥤ D) (R : C' ⥤ D')
    (A : Type u) [Ring A] (H : D' ⥤ ModuleCat.{u} A)
    (α : G ⋙ M ⟶ L ⋙ R) (P J : C) (z : H.obj (M.obj (G.obj P)))
    (hL : Function.Bijective (L.map : (P ⟶ J) → (L.obj P ⟶ L.obj J)))
    (hG : Function.Bijective (G.map : (P ⟶ J) → (G.obj P ⟶ G.obj J)))
    (hM : Function.Bijective (M.map : (G.obj P ⟶ G.obj J) →
      (M.obj (G.obj P) ⟶ M.obj (G.obj J))))
    (hEval : Function.Bijective (fun f : M.obj (G.obj P) ⟶ M.obj (G.obj J) ↦ H.map f z))
    [IsIso (α.app J)] :
    Function.Bijective (fun f : L.obj P ⟶ L.obj J ↦
      H.map (R.map f) (H.map (α.app P) z)) := by
  have h := (ConcreteCategory.bijective_of_isIso (H.map (α.app J))).comp
    (hEval.comp (hM.comp hG))
  have hn (f : P ⟶ J) :
      H.map (α.app J) (H.map (M.map (G.map f)) z) =
        H.map (R.map (L.map f)) (H.map (α.app P) z) := by
    change (H.map (M.map (G.map f)) ≫ H.map (α.app J)) z =
      (H.map (α.app P) ≫ H.map (R.map (L.map f))) z
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg (fun k ↦ H.map k z) (α.naturality f)
  have hh : Function.Bijective ((fun f : L.obj P ⟶ L.obj J ↦
      H.map (R.map f) (H.map (α.app P) z)) ∘ L.map) := by
    simpa only [Function.comp_def, hn] using h
  exact (Function.Bijective.of_comp_iff _ hL).mp hh

private theorem evaluation_bijective_transport
    {C : Type*} [Category C] (A : Type u) [Ring A] (F : C ⥤ ModuleCat.{u} A)
    {S S' E E' : C} (s : S ≅ S') (e : E ≅ E') (z : F.obj S')
    (h : Function.Bijective (fun f : S' ⟶ E' ↦ F.map f z)) :
    Function.Bijective (fun f : S ⟶ E ↦ F.map f (F.map s.inv z)) := by
  have hh := (ConcreteCategory.bijective_of_isIso (F.map e.inv)).comp
    (h.comp (Iso.homCongr s e).bijective)
  convert hh using 1
  funext f
  change F.map f (F.map s.inv z) = F.map e.inv (F.map (s.inv ≫ f ≫ e.hom) z)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.map_comp, ← F.map_comp]
  simp only [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The class of one in derived global sections of the degree-zero structure sheaf.
It is constructed before choosing a resolution, using the ordinary-to-derived unit.
Source: Stacks Project, Tag 079V, K-injective computation of derived global sections.
(blueprint: lem-sc-derived-structure-evaluation-one-bijective). -/
def derivedStructureGlobalOne (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0).obj
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings X.toRingedSpace)))) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let A := (moduleRings X.toRingedSpace).obj.obj (op ⊤)
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  let F := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let T := (CochainComplex.singleFunctor C 0).obj
    (SheafOfModules.unit (moduleRings X.toRingedSpace))
  let S := (F.mapHomologicalComplex (.up ℤ)).obj T
  let ε : S.homology 0 ≅ ModuleCat.of A A :=
    (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A A)
  let β : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) F.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      F.rightDerivedFunctor).hom
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (β.app T)
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app S).inv
      (ε.inv (1 : A)))

/-- Canonical evaluation at one is bijective, without any open-restriction comparison.
Source: Stacks Project, Tag 09M1, the structure-sheaf case of the first Hom formula;
Tag 079V, computation by K-injective complexes.
(blueprint: lem-sc-derived-structure-evaluation-one-bijective).

Proof: Resolve E by a K-injective complex J. Localization identifies maps from
O_X[0] to E with homotopy classes of maps O_X[0] to J. Such a map is determined
by its value on one in degree zero: a global cycle. Conversely a global cycle
z defines the map r ↦ r z, with z restricted to each open. These operations are
inverse. A homotopy is exactly a degree minus one global section whose boundary
is the difference of the cycles. Thus the quotient is H^0 of global sections
of J. The ordinary-to-derived comparison is an isomorphism on J. Naturality
of this comparison with the resolution identifies this cycle evaluation with
H^0(RΓ(f)) applied to the displayed, explicitly constructed class of one.
Changing representatives preserves both maps, and gives the asserted bijection
on the specified derived category. The zero ring and empty scheme give zero
modules and the same argument; no boundedness or quasi-coherence is used. -/
theorem derivedStructure_evaluation_one_bijective (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let F := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶ E ↦
      F.map f (derivedStructureGlobalOne X)) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let A := (moduleRings X.toRingedSpace).obj.obj (op ⊤)
  let D := ModuleCat.{u} A
  let := HasDerivedCategory.standard D
  let F := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let G := F.mapHomotopyCategory (.up ℤ)
  let L := DerivedCategory.Qh (C := C)
  let M := DerivedCategory.Qh (C := D)
  let R := F.rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor D 0
  let T := (CochainComplex.singleFunctor C 0).obj
    (SheafOfModules.unit (moduleRings X.toRingedSpace))
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj T
  let Z : CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj T
  let V := (CochainComplex.singleFunctor D 0).obj (ModuleCat.of A A)
  let b : Z ≅ V := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _
  have hV (n : ℤ) : Projective (V.X n) := by
    by_cases hn : n = 0
    · subst n
      change Projective (ModuleCat.of A A)
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ)
        0 (ModuleCat.of A A) n hn).projective
  let _ := hV
  have : V.IsKProjective := CochainComplex.isKProjective_of_projective V 0
  have : Z.IsKProjective := CochainComplex.isKProjective_of_iso b.symm
  let γ : M.obj (G.obj P) ≅ DerivedCategory.Q.obj Z :=
    (DerivedCategory.quotientCompQhIso D).app Z
  let ε₀ : Z.homology 0 ≅ ModuleCat.of A A :=
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).mapIso b ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A A)
  let ε : H.obj (M.obj (G.obj P)) ≅ ModuleCat.of A A :=
    H.mapIso γ ≪≫ (DerivedCategory.homologyFunctorFactors D 0).app Z ≪≫ ε₀
  let σ : (DerivedCategory.singleFunctor C 0).obj
      (SheafOfModules.unit (moduleRings X.toRingedSpace)) ≅ L.obj P :=
    (DerivedCategory.quotientCompQhIso C).symm.app T
  let α := F.rightDerivedFunctorUnit
  obtain ⟨J, hJ, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective E
  let _ := hJ
  let Jₕ := (HomotopyCategory.quotient C (.up ℤ)).obj J
  let e : E ≅ L.obj Jₕ := i ≪≫ (DerivedCategory.quotientCompQhIso C).symm.app J
  have hL : Function.Bijective (L.map : (P ⟶ Jₕ) → (L.obj P ⟶ L.obj Jₕ)) :=
    CochainComplex.IsKInjective.Qh_map_bijective P J
  have hG : Function.Bijective (G.map : (P ⟶ Jₕ) → (G.obj P ⟶ G.obj Jₕ)) :=
    global_homotopy_map_bijective X.toRingedSpace Jₕ
  have hM : Function.Bijective (M.map : (G.obj P ⟶ G.obj Jₕ) →
      (M.obj (G.obj P) ⟶ M.obj (G.obj Jₕ))) :=
    CochainComplex.IsKProjective.Qh_map_bijective Z (G.obj Jₕ)
  have hEval : Function.Bijective (fun f : M.obj (G.obj P) ⟶ M.obj (G.obj Jₕ) ↦
      H.map f (ε.inv (1 : A))) :=
    free_evaluation_bijective A _ _ (γ ≪≫ DerivedCategory.Q.mapIso b) ε
  have h := evaluation_bijective_of_unit L M G R A H α P Jₕ
    (ε.inv (1 : A)) hL hG hM hEval
  have hOne : derivedStructureGlobalOne X =
      H.map (R.map σ.inv) (H.map (α.app P) (ε.inv (1 : A))) := by
    change H.map (γ.inv ≫ α.app P ≫ R.map σ.inv)
        (((DerivedCategory.homologyFunctorFactors D 0).app Z).inv (ε₀.inv (1 : A))) = _
    simp only [H.map_comp]
    rfl
  have ht := evaluation_bijective_transport A (R ⋙ H) σ e
    (H.map (α.app P) (ε.inv (1 : A))) h
  change Function.Bijective (fun f :
    (DerivedCategory.singleFunctor C 0).obj
      (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶ E ↦
      H.map (R.map f) (derivedStructureGlobalOne X))
  rw [hOne]
  exact ht

end
end AlgebraicGeometry
