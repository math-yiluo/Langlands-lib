/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates
public import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Localization.BaseChange

/-! # Scalar extension coordinates for exact affine stalk homology

Source: Stacks Project, Tags 01I9 and 01AG.
(blueprint: lem-pc-affine-stalk-scalar-extension-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

private def stalkExtensionIso (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    (V : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (StructureSheaf.toStalk A p).hom).obj V ≅
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).obj
        (tilde.functor (.of A) |>.obj V) := by
  let D : Type u := (structurePresheafInCommRingCat A).stalk p
  let e := (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl D
    (StructureSheaf.toStalkₗ A V p)).equiv
  exact e.toModuleIso

private theorem stalkExtensionIso_one (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    (V : ModuleCat.{u} A) (x : V) :
    (stalkExtensionIso A p V).hom ((1 : (Spec (.of A)).presheaf.stalk p)
      ⊗ₜ[A, (StructureSheaf.toStalk A p).hom] x) = StructureSheaf.toStalkₗ A V p x := by
  change (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
    ((structurePresheafInCommRingCat A).stalk p) (StructureSheaf.toStalkₗ A V p)).equiv
      (1 ⊗ₜ[A] x) = _
  rw [IsBaseChange.equiv_tmul, one_smul]

private theorem stalkExtensionIso_naturality
    (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    {U V : ModuleCat.{u} A} (a : U ⟶ V) :
    (ModuleCat.extendScalars (StructureSheaf.toStalk A p).hom).map a ≫
        (stalkExtensionIso A p V).hom =
      (stalkExtensionIso A p U).hom ≫
        (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map
          ((tilde.functor (.of A)).map a) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (stalkExtensionIso A p V).hom
      ((ModuleCat.extendScalars (StructureSheaf.toStalk A p).hom).map a
        ((1 : (Spec (.of A)).presheaf.stalk p) ⊗ₜ[A, (StructureSheaf.toStalk A p).hom] x)) =
    (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map
      ((tilde.functor (.of A)).map a)
      ((stalkExtensionIso A p U).hom
        ((1 : (Spec (.of A)).presheaf.stalk p) ⊗ₜ[A, (StructureSheaf.toStalk A p).hom] x))
  rw [ModuleCat.ExtendScalars.map_tmul, stalkExtensionIso_one]
  change _ = ((RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map
    ((tilde.functor (.of A)).map a)) ((stalkExtensionIso A p U).hom _)
  rw [stalkExtensionIso_one]
  dsimp only [StructureSheaf.toStalkₗ, RingedSpace.moduleStalkFunctor,
    RingedSpace.moduleStalkMap, RingedSpace.stalkAddMap]
  change _ = (TopCat.Presheaf.stalkFunctor Ab.{u} p).map
    ((PresheafOfModules.toPresheaf _).map (tilde.map (R := .of A) a).val)
      (TopCat.Presheaf.germ (moduleStructurePresheaf A U).presheaf ⊤ p
        (by simp) (StructureSheaf.toOpenₗ A U ⊤ x))
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h := tilde.toOpen_map_app (R := .of A) a ⊤
  have h' := congr($h x)
  change TopCat.Presheaf.germ (moduleStructurePresheaf A V).presheaf ⊤ p _ _ =
    TopCat.Presheaf.germ (moduleStructurePresheaf A V).presheaf ⊤ p _ _
  exact congrArg (fun z ↦ TopCat.Presheaf.germ (moduleStructurePresheaf A V).presheaf
    ⊤ p trivial z) h'.symm

/-- The localization equivalence commutes with maps of modules. -/
private theorem stalkLocalizationIso_naturality
    (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    {U V : ModuleCat.{u} A} (a : U ⟶ V)
    (x : LocalizedModule p.asIdeal.primeCompl U) :
    (IsLocalizedModule.iso p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A V p))
        (LocalizedModule.map p.asIdeal.primeCompl a.hom x) =
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map
        ((tilde.functor (.of A)).map a)
        ((IsLocalizedModule.iso p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A U p)) x) := by
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p
  let TB := tilde.functor (.of A)
  let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk A p).hom
  let t : U →ₗ[A] (Rs.obj (s.obj (TB.obj U))) := StructureSheaf.toStalkₗ A U p
  let t' : V →ₗ[A] (Rs.obj (s.obj (TB.obj V))) := StructureSheaf.toStalkₗ A V p
  have : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A U p))
  have : IsLocalizedModule p.asIdeal.primeCompl t' :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A V p))
  have hmap : (Rs.map (s.map (TB.map a))).hom =
      IsLocalizedModule.map p.asIdeal.primeCompl t t' a.hom := by
    apply IsLocalizedModule.ext p.asIdeal.primeCompl t (IsLocalizedModule.map_units t')
    ext y
    have hn := congrArg (fun k ↦ k
      ((1 : (Spec.structureSheaf A).presheaf.stalk p)
        ⊗ₜ[A, (StructureSheaf.toStalk A p).hom] y))
      (stalkExtensionIso_naturality A p a)
    simp only [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul] at hn
    rw [stalkExtensionIso_one A p V (a y), stalkExtensionIso_one A p U y] at hn
    exact hn.symm.trans
      (IsLocalizedModule.map_apply p.asIdeal.primeCompl t t' a.hom y).symm
  have hloc := congrArg (fun z ↦ z x)
    (IsLocalizedModule.map_iso_commute p.asIdeal.primeCompl t t' a.hom)
  rw [← hmap] at hloc
  exact hloc.symm

private theorem homology_pi_map
    {B E : Type*} [Category B] [Category E]
    [HasZeroMorphisms B] [HasZeroMorphisms E]
    (S : ShortComplex B) [S.HasHomology]
    (F : B ⥤ E) [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [ShortComplex.LeftHomologyData.mapCyclesIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

private theorem homology_comp_iso
    {B E H : Type*} [Category B] [Category E] [Category H]
    [Abelian B] [Abelian E] [Abelian H]
    (S : ShortComplex B) [S.HasHomology]
    (F : B ⥤ E) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (G : E ⥤ H) [G.PreservesZeroMorphisms] [G.PreservesHomology]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  have hc : ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom =
      (S.mapCyclesIso (F ⋙ G)).hom := by
    apply (cancel_mono ((F ⋙ G).map S.iCycles)).1
    simp only [Category.assoc, Functor.comp_map, ← G.map_comp,
      ShortComplex.mapCyclesIso_hom_iCycles]
    exact (ShortComplex.mapCyclesIso_hom_iCycles S (F ⋙ G)).symm
  apply (cancel_epi ((S.map (F ⋙ G)).homologyπ)).1
  have h₁ := homology_pi_map (S.map F) G
  have h₂ := homology_pi_map S F
  have h₃ := homology_pi_map S (F ⋙ G)
  change ((S.map F).map G).homologyπ ≫
      (((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom) = _
  calc
    _ = ((S.map F).mapCyclesIso G).hom ≫
        (G.map (S.map F).homologyπ ≫ G.map (S.mapHomologyIso F).hom) := by
      rw [← Category.assoc, h₁, Category.assoc]
    _ = ((S.map F).mapCyclesIso G).hom ≫
        G.map ((S.mapCyclesIso F).hom ≫ F.map S.homologyπ) := by
      rw [← G.map_comp, h₂]
    _ = (S.mapCyclesIso (F ⋙ G)).hom ≫ (F ⋙ G).map S.homologyπ := by
      rw [G.map_comp, ← Category.assoc, hc]
      rfl
    _ = _ := h₃.symm

/-- Naturality of homology followed by the inverses for a composite exact functor. -/
private theorem homology_composite_naturality
    {B E H : Type*} [Category B] [Category E] [Category H]
    [Abelian B] [Abelian E] [Abelian H]
    (S : ShortComplex B) [S.HasHomology]
    (F : B ⥤ H) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (T : B ⥤ E) [T.PreservesZeroMorphisms] [T.PreservesHomology]
    (G : E ⥤ H) [G.PreservesZeroMorphisms] [G.PreservesHomology]
    [PreservesFiniteLimits (T ⋙ G)] [PreservesFiniteColimits (T ⋙ G)]
    (θ : F ≅ T ⋙ G) :
    θ.hom.app S.homology ≫ G.map (S.mapHomologyIso T).inv ≫
        ((S.map T).mapHomologyIso G).inv =
      (S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap (S.mapNatTrans θ.hom) := by
  have hcomp := homology_comp_iso S T G
  have htail : (S.mapHomologyIso (T ⋙ G)).hom ≫
      G.map (S.mapHomologyIso T).inv ≫ ((S.map T).mapHomologyIso G).inv = 𝟙 _ := by
    calc
      _ = ((S.map T).mapHomologyIso G).hom ≫
          (G.map (S.mapHomologyIso T).hom ≫ G.map (S.mapHomologyIso T).inv) ≫
          ((S.map T).mapHomologyIso G).inv := by
        rw [← hcomp]
        simp only [Category.assoc]
      _ = _ := by
        rw [← G.map_comp, Iso.hom_inv_id, G.map_id]
        simp only [Category.id_comp, Iso.hom_inv_id]
        rfl
  rw [θ.hom.app_homology S]
  simp only [Category.assoc]
  rw [htail, Category.comp_id]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Exact affine stalk homology in scalar-extension coordinates, natural for every
module map into ordinary cohomology. Source: Stacks Project, Tags 01I9 and 01AG.
(blueprint: lem-pc-affine-stalk-scalar-extension-coordinates).

Proof: the structure-sheaf stalk D is the localization of A at p. For every
A-module V, the map to the stalk of tilde V is a module localization. Its
base-change universal property gives a D-linear isomorphism D tensor_A V to
that stalk, sending 1 tensor v to the germ of v. Naturality on these generators
proves naturality on all tensors. Apply this natural isomorphism termwise to C
to obtain chi. The canonical localization of V also identifies with D tensor_A V;
call this additive equivalence e(V). The two identifications agree on numerators,
hence on all fractions. Exact scalar extension, exact tilde, and exact stalks
commute with homology. Naturality of their homology isomorphisms identifies
homology(chi) with the composite defining affineTildeHomologyLocalization.
Naturality of e for a gives the displayed equation. No derived tensor source,
K-flatness, or cartesian square is used. Zero modules and complexes obey the
same argument; if A is zero there is no p. -/
theorem exists_affineStalkScalarExtensionCoordinates
    (A : Type u) [CommRing A] (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (p : PrimeSpectrum A) (i : ℤ) :
    let D : Type u := (Spec.structureSheaf A).presheaf.stalk p
    let κ := (StructureSheaf.toStalk A p).hom
    let F := ModuleCat.extendScalars κ
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat D p.asIdeal.primeCompl))
    let N := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj C)
    let s := RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p
    ∃ χ : (F.mapHomologicalComplex (.up ℤ)).obj C ≅
        (s.mapHomologicalComplex (.up ℤ)).obj N,
      (∀ (j : ℤ) (x : C.X j), χ.hom.f j ((1 : D) ⊗ₜ[A, κ] x) =
        TopCat.Presheaf.germ (N.X j).val.presheaf ⊤ p trivial
          (tilde.toOpen (R := .of A) (C.X j) ⊤ x)) ∧
      ∃ e : ∀ U : ModuleCat.{u} A,
          LocalizedModule p.asIdeal.primeCompl U ≃+ F.obj U,
        ∀ (U : ModuleCat.{u} A) (a : U ⟶ C.homology i) (x),
          affineTildeHomologyLocalization A C p i
              (LocalizedModule.map p.asIdeal.primeCompl a.hom x) =
            HomologicalComplex.homologyMap χ.hom i
              (((C.sc i).mapHomologyIso F).inv (F.map a (e U x)))  := by
  dsimp only
  let F := ModuleCat.extendScalars (StructureSheaf.toStalk A p).hom
  let TB : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p
  have : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat ((Spec.structureSheaf A).presheaf.stalk p)
          p.asIdeal.primeCompl))
  let : TB.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology A
  let : s.PreservesZeroMorphisms := inferInstance
  let : (TB ⋙ s).PreservesZeroMorphisms := ⟨fun _ _ ↦ by simp⟩
  have : s.PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro T hT
    exact ((RingedSpace.module_stalk_exact (Spec (.of A)).toRingedSpace T.f).2.2.2.2
      T.X₃ T.f T.g T.zero).mp hT p
  let θ : F ≅ TB ⋙ s := NatIso.ofComponents
    (stalkExtensionIso A p) (fun a ↦ stalkExtensionIso_naturality A p a)
  have : PreservesFiniteLimits (TB ⋙ s) := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits (TB ⋙ s) := preservesFiniteColimits_of_natIso θ
  let χ : (F.mapHomologicalComplex (.up ℤ)).obj C ≅
      (s.mapHomologicalComplex (.up ℤ)).obj ((TB.mapHomologicalComplex (.up ℤ)).obj C) :=
    HomologicalComplex.Hom.isoOfComponents (fun j ↦ stalkExtensionIso A p (C.X j))
      (fun j k _ ↦ (stalkExtensionIso_naturality A p (C.d j k)).symm)
  refine ⟨χ, ?_, ?_⟩
  · intro j x
    change (stalkExtensionIso A p (C.X j)).hom _ = _
    exact stalkExtensionIso_one A p (C.X j) x
  · let e := fun U : ModuleCat.{u} A ↦
      (IsLocalizedModule.iso p.asIdeal.primeCompl
        (StructureSheaf.toStalkₗ A U p)).toAddEquiv.trans
          (θ.app U).symm.toLinearEquiv.toAddEquiv
    refine ⟨e, ?_⟩
    intro U a x
    let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk A p).hom
    let t : U →ₗ[A] (Rs.obj (s.obj (TB.obj U))) := StructureSheaf.toStalkₗ A U p
    let t' : C.homology i →ₗ[A] (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
      StructureSheaf.toStalkₗ A (C.homology i) p
    have : IsLocalizedModule p.asIdeal.primeCompl t :=
      inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A U p))
    have : IsLocalizedModule p.asIdeal.primeCompl t' :=
      inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
        (StructureSheaf.toStalkₗ A (C.homology i) p))
    have hloc := stalkLocalizationIso_naturality A p a x
    have hn := congrArg (fun k ↦ k (e U x)) (θ.hom.naturality a)
    change (θ.app (C.homology i)).hom (F.map a (e U x)) =
      s.map (TB.map a) ((θ.app U).hom (e U x)) at hn
    have hsource : (θ.app U).hom (e U x) = (IsLocalizedModule.iso p.asIdeal.primeCompl t) x := by
      change (θ.app U).hom ((θ.app U).inv _) = _
      exact (θ.app U).toLinearEquiv.apply_symm_apply _
    rw [hsource] at hn
    have hnum : (IsLocalizedModule.iso p.asIdeal.primeCompl t')
        (LocalizedModule.map p.asIdeal.primeCompl a.hom x) =
      (θ.app (C.homology i)).hom (F.map a (e U x)) := hloc.trans hn.symm
    have hH : (θ.app (C.homology i)).hom ≫
        s.map ((C.sc i).mapHomologyIso TB).inv ≫
        ((((TB.mapHomologicalComplex (.up ℤ)).obj C).sc i).mapHomologyIso s).inv =
      ((C.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap χ.hom i :=
      homology_composite_naturality (C.sc i) F TB s θ
    have hz : ∀ y : LocalizedModule p.asIdeal.primeCompl (C.homology i),
        affineTildeHomologyLocalization A C p i y =
          ((((TB.mapHomologicalComplex (.up ℤ)).obj C).sc i).mapHomologyIso s).inv
            (s.map ((C.sc i).mapHomologyIso TB).inv
              ((IsLocalizedModule.iso p.asIdeal.primeCompl t') y)) := by
      intro y
      let N := (TB.mapHomologicalComplex (.up ℤ)).obj C
      let δ := (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).app N
      change (s.map δ.hom ≫ (N.sc i |>.mapHomologyIso s).inv)
          (s.map (((C.sc i).mapHomologyIso TB).inv ≫ δ.inv)
            ((IsLocalizedModule.iso p.asIdeal.primeCompl t') y)) = _
      rw [s.map_comp]
      change (N.sc i |>.mapHomologyIso s).inv
          ((s.mapIso δ).hom ((s.mapIso δ).inv
            (s.map ((C.sc i).mapHomologyIso TB).inv
              ((IsLocalizedModule.iso p.asIdeal.primeCompl t') y)))) = _
      exact congrArg (fun z ↦ ((N.sc i).mapHomologyIso s).inv z)
        ((s.mapIso δ).toLinearEquiv.apply_symm_apply _)
    rw [hz, hnum]
    have hv := congrArg (fun k ↦ k (F.map a (e U x))) hH
    simp only [ModuleCat.comp_apply] at hv
    exact hv

end AlgebraicGeometry
