/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.ModuleStalkExact
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Natural module presentations of affine derived cohomology

Source: Stacks Project, Tags 06Z0 and 0DJ8.
(blueprint: lem-pc-affine-derived-cohomology-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Actual global sections of a quasi-coherent cohomology sheaf, with the canonical
module action. Source: Stacks, Tag 06Z0.
(blueprint: lem-pc-affine-derived-cohomology-presentation). -/
def affineDerivedCohomologyModules (A : Type u) [CommRing A] (i : ℤ) :
    schemeDerivedQCohCategory (Spec (.of A)) ⥤ ModuleCat.{u} A :=
  (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
    moduleSpecΓFunctor (R := .of A)

/-- Canonical localization of global sections to derived stalk cohomology.
Source: Stacks, Tags 01HV and 06Z0; exactness of stalks.
(blueprint: lem-pc-affine-derived-cohomology-presentation). -/
def affineDerivedCohomologyStalkIso (A : Type u) [CommRing A] (i : ℤ)
    (p : PrimeSpectrum A) (L : schemeDerivedQCohCategory (Spec (.of A))) :
    LocalizedModule p.asIdeal.primeCompl
      ((affineDerivedCohomologyModules A i).obj L) ≃+
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L.obj) := by
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L.obj
  have : M.IsQuasicoherent := L.property i
  let G := (moduleSpecΓFunctor (R := .of A)).obj M
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p
  have he : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) M
  let e := s.mapIso (asIso (Scheme.Modules.fromTildeΓ (R := .of A) M))
  let l := IsLocalizedModule.iso p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A G p)
  exact l.toAddEquiv.trans (CategoryTheory.Iso.toLinearEquiv e).toAddEquiv

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- (blueprint: lem-pc-affine-derived-cohomology-presentation) -/
private theorem affineTildeStalk_naturality (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) {U V : ModuleCat.{u} A} (a : U ⟶ V) (x : U) :
    (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map
      (tilde.map (R := .of A) a) (StructureSheaf.toStalkₗ A U p x) =
        StructureSheaf.toStalkₗ A V p (a x) := by
  dsimp only [StructureSheaf.toStalkₗ, RingedSpace.moduleStalkFunctor,
    RingedSpace.moduleStalkMap, RingedSpace.stalkAddMap]
  change (TopCat.Presheaf.stalkFunctor Ab.{u} p).map
    ((PresheafOfModules.toPresheaf _).map (tilde.map (R := .of A) a).val)
      (TopCat.Presheaf.germ (moduleStructurePresheaf A U).presheaf ⊤ p
        (by simp) (StructureSheaf.toOpenₗ A U ⊤ x)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h := tilde.toOpen_map_app (R := .of A) a ⊤
  have h' := congr($h x)
  change TopCat.Presheaf.germ (moduleStructurePresheaf A V).presheaf ⊤ p _ _ =
    TopCat.Presheaf.germ (moduleStructurePresheaf A V).presheaf ⊤ p _ _
  congr 1

/-- Localization of global sections is natural for morphisms in the affine derived
quasi-coherent category. Source: Stacks, Tag 01HV.
(blueprint: lem-pc-affine-derived-cohomology-presentation). -/
theorem affineDerivedCohomologyStalkIso_naturality
    (A : Type u) [CommRing A] (i : ℤ) (p : PrimeSpectrum A)
    {L N : schemeDerivedQCohCategory (Spec (.of A))} (a : L ⟶ N)
    (x : LocalizedModule p.asIdeal.primeCompl
      ((affineDerivedCohomologyModules A i).obj L)) :
    affineDerivedCohomologyStalkIso A i p N
        (LocalizedModule.map p.asIdeal.primeCompl
          ((affineDerivedCohomologyModules A i).map a).hom x) =
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).map a.hom)
        (affineDerivedCohomologyStalkIso A i p L x) := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  let M := H.obj L.obj
  let M' := H.obj N.obj
  let G := (moduleSpecΓFunctor (R := .of A)).obj M
  let G' := (moduleSpecΓFunctor (R := .of A)).obj M'
  let b := (moduleSpecΓFunctor (R := .of A)).map (H.map a.hom)
  let st := RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p
  let Rst := ModuleCat.restrictScalars (StructureSheaf.toStalk A p).hom
  let t : G →ₗ[A] (Rst.obj (st.obj (tilde (R := .of A) G))) :=
    StructureSheaf.toStalkₗ A G p
  let t' : G' →ₗ[A] (Rst.obj (st.obj (tilde (R := .of A) G'))) :=
    StructureSheaf.toStalkₗ A G' p
  have ht : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A G p))
  have ht' : IsLocalizedModule p.asIdeal.primeCompl t' :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A G' p))
  have hmap : (Rst.map (st.map (tilde.map b))).hom =
      IsLocalizedModule.map p.asIdeal.primeCompl t t' b.hom := by
    apply IsLocalizedModule.ext p.asIdeal.primeCompl t (IsLocalizedModule.map_units t')
    ext y
    exact (affineTildeStalk_naturality A p b y).trans
      (IsLocalizedModule.map_apply p.asIdeal.primeCompl t t' b.hom y).symm
  have hloc := congrArg (fun z => z x)
    (IsLocalizedModule.map_iso_commute p.asIdeal.primeCompl t t' b.hom)
  have hloc' : st.map (tilde.map b) ((IsLocalizedModule.iso p.asIdeal.primeCompl t) x) =
      (IsLocalizedModule.iso p.asIdeal.primeCompl t')
        (LocalizedModule.map p.asIdeal.primeCompl b.hom x) := by
    rw [← hmap] at hloc
    exact hloc
  have hn := (Scheme.Modules.fromTildeΓNatTrans (R := .of A)).naturality (H.map a.hom)
  have hn' := congrArg (fun z => st.map z) hn
  rw [Functor.map_comp, Functor.map_comp] at hn'
  have hv := congrArg (fun z => z ((IsLocalizedModule.iso p.asIdeal.primeCompl t) x)) hn'
  change st.map (Scheme.Modules.fromTildeΓ (R := .of A) M')
      ((IsLocalizedModule.iso p.asIdeal.primeCompl t')
        (LocalizedModule.map p.asIdeal.primeCompl b.hom x)) =
    st.map (H.map a.hom)
      (st.map (Scheme.Modules.fromTildeΓ (R := .of A) M)
        ((IsLocalizedModule.iso p.asIdeal.primeCompl t) x))
  rw [← hloc']
  exact hv

/-- Exact stalks identify the cohomology of a representative with stalk cohomology.
Source: Stacks, Tag 01AG.
(blueprint: lem-pc-affine-derived-cohomology-presentation). -/
def affineRepresentativeStalkIso (Y : Scheme.{u}) (p : Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (i : ℤ) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace p).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
            (DerivedCategory.Q.obj P)) ≅
      (((RingedSpace.moduleStalkFunctor Y.toRingedSpace p).mapHomologicalComplex
        (.up ℤ)).obj P).homology i := by
  let s := RingedSpace.moduleStalkFunctor Y.toRingedSpace p
  have : s.PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro T hT
    exact ((RingedSpace.module_stalk_exact Y.toRingedSpace T.f).2.2.2.2
      T.X₃ T.f T.g T.zero).mp hT p
  exact s.mapIso ((DerivedCategory.homologyFunctorFactors _ i).app P) ≪≫
    ((P.sc i).mapHomologyIso s).symm

/-- Naturality of the exact stalk/representative comparison.
Source: Stacks, Tag 01AG.
(blueprint: lem-pc-affine-derived-cohomology-presentation). -/
@[reassoc]
theorem affineRepresentativeStalkIso_naturality (Y : Scheme.{u}) (p : Y)
    {P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (a : P ⟶ N) (i : ℤ) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace p).map
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).map
            (DerivedCategory.Q.map a)) ≫ (affineRepresentativeStalkIso Y p N i).hom =
      (affineRepresentativeStalkIso Y p P i).hom ≫
        HomologicalComplex.homologyMap
          (((RingedSpace.moduleStalkFunctor Y.toRingedSpace p).mapHomologicalComplex
            (.up ℤ)).map a) i := by
  dsimp only [affineRepresentativeStalkIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    DerivedCategory.homologyFunctorFactors_hom_naturality, Functor.map_comp,
    Category.assoc]
  have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace p).PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro T hT
    exact ((RingedSpace.module_stalk_exact Y.toRingedSpace T.f).2.2.2.2
      T.X₃ T.f T.g T.zero).mp hT p
  have hs := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map a)
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace p)
  have hs' : (RingedSpace.moduleStalkFunctor Y.toRingedSpace p).map
      (HomologicalComplex.homologyMap a i) ≫
        ((N.sc i).mapHomologyIso (RingedSpace.moduleStalkFunctor Y.toRingedSpace p)).inv =
      ((P.sc i).mapHomologyIso (RingedSpace.moduleStalkFunctor Y.toRingedSpace p)).inv ≫
        HomologicalComplex.homologyMap
          (((RingedSpace.moduleStalkFunctor Y.toRingedSpace p).mapHomologicalComplex
            (.up ℤ)).map a) i := hs
  rw [hs', Category.assoc]

end AlgebraicGeometry
