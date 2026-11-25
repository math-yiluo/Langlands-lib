/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.Algebra.Homology.AffineTensorPullbackHomologySheafIso
import WeilConjectures.Algebra.Homology.AffineTildeGlobalSectionsStalkCoordinates
import WeilConjectures.Algebra.Homology.AffineBaseChangeGlobalSectionsFactorization

/-! # AffineTensorPullbackStalkCoordinates

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The additive equivalence of a module isomorphism.
Source: Mathlib, `CategoryTheory.Iso.toLinearEquiv`.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates). -/
def affineModuleIsoAddEquiv {R : Type u} [Ring R]
    {U V : ModuleCat.{u} R} (d : U ≅ V) : U ≃+ V where
  toFun := d.hom
  invFun := d.inv
  left_inv x := by
    exact ConcreteCategory.congr_hom d.hom_inv_id x
  right_inv x := by
    exact ConcreteCategory.congr_hom d.inv_hom_id x
  map_add' x y := d.hom.hom.map_add x y

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- Forward-map equation for the module-isomorphism additive equivalence.
Source: Mathlib, `CategoryTheory.Iso.toLinearEquiv_apply`.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates). -/
theorem affineModuleIsoAddEquiv_coe {R : Type u} [Ring R]
    {U V : ModuleCat.{u} R} (d : U ≅ V) :
    ⇑(affineModuleIsoAddEquiv d) = d.hom := by
  rfl

/-- Localization followed by a specified sheaf isomorphism at an affine stalk.
Source: Stacks Project, Tag 01HV.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates). -/
def affineTildeLocalizationStalkIso (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) (V : ModuleCat.{u} A) (W : (Spec (.of A)).Modules)
    (d : (tilde.functor (.of A)).obj V ≅ W) :
    LocalizedModule p.asIdeal.primeCompl V ≃+
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).obj W :=
  (IsLocalizedModule.iso p.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ A V p)).toAddEquiv.trans
      (affineModuleIsoAddEquiv
        ((RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).mapIso d))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- Forward map of localization followed by the stalk of a sheaf isomorphism.
Source: Stacks Project, Tag 01HV.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates). -/
theorem affineTildeLocalizationStalkIso_apply (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) (V : ModuleCat.{u} A) (W : (Spec (.of A)).Modules)
    (d : (tilde.functor (.of A)).obj V ≅ W)
    (x : LocalizedModule p.asIdeal.primeCompl V) :
    affineTildeLocalizationStalkIso A p V W d x =
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map d.hom
        ((IsLocalizedModule.iso p.asIdeal.primeCompl
          (StructureSheaf.toStalkₗ A V p)) x) := by
  rfl

/-- (blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates) -/
def affineTensorPullbackHomologyStalkIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : PrimeSpectrum A') (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φ))).mapHomologicalComplex (.up ℤ)).obj P
    LocalizedModule p.asIdeal.primeCompl
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i) ≃+
        (RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).obj
              (DerivedCategory.Q.obj T)) := by
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
  let l := IsLocalizedModule.iso p.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ A' (C.homology i) p)
  -- Keep the original equivalence projections visible to definitional consumers.
  exact l.toAddEquiv.trans
    (s.mapIso (affineTensorPullbackHomologySheafIso A A' φ M i)).toLinearEquiv.toAddEquiv


/-- Affine localization identifies the base-change coordinate with the stalk map
of the inverse ordinary pullback counit.  This is the geometric localization
identity from Stacks Tag 0DJ8; the remaining supplied representative isomorphism
is handled by functoriality in the main theorem.
(blueprint: new-lem-pc-affine-tensor-pullback-stalk-coordinates-at).
Proof: expand affine localization and stalk coordinates; the adjunction triangle and
naturality of the localization germ map identify the inverse counit component. Apply
the supplied representative isomorphism by functoriality. This works for arbitrary
complexes and degrees, including zero objects. -/
theorem affineTensorPullbackHomologyStalkIso_counit_coordinate
    (A A' : Type u) [CommRing A] [CommRing A'] (φg' : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
    (p : PrimeSpectrum A') :
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
      Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φg'))
    letI : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w}
      (Spec.map (CommRingCat.ofHom φg'))
    let c :=
      (DerivedCategory.quotientCompQhIso.{w} _).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
      inv ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map
        ((DerivedCategory.quotientCompQhIso _).hom.app P)
    let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
    let z := fun y => s.map (H.map c)
      (affineTensorPullbackHomologyStalkIso A A' φg' M p i y)
    ∀ y, affineDerivedCohomologyStalkIso A' i p L
        (LocalizedModule.map p.asIdeal.primeCompl b.hom.hom y) =
      s.map (H.map ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map e.hom))
        (z y) := by
  -- Keep the composite c shared when applying the stalk-coordinate identity.
  intro L b P H E c s z y
  let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
  let d₀ := affineTensorPullbackHomologySheafIso A A' φg' M i
  let a := (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map e.hom
  change affineDerivedCohomologyStalkIso A' i p L
      (LocalizedModule.map p.asIdeal.primeCompl b.hom.hom y) =
    s.map (H.map a) (s.map (H.map c)
      (affineTensorPullbackHomologyStalkIso A A' φg' M p i y))
  have h := affineTildeGlobalSectionsStalk_coordinates A' i p L (C.homology i)
    (d₀.hom ≫ H.map c ≫ H.map a) y
  have hb := affineBaseChangeTildeCohomologyIso_globalSections_factorization
    A A' φg' K M e hc i
  calc
    _ = s.map (d₀.hom ≫ H.map c ≫ H.map a)
        ((IsLocalizedModule.iso p.asIdeal.primeCompl
          (StructureSheaf.toStalkₗ A' (C.homology i) p)) y) := by
      simpa only [b, hb] using h
    _ = _ := by
      change _ = s.map (H.map a) (s.map (H.map c)
        (s.map d₀.hom ((IsLocalizedModule.iso p.asIdeal.primeCompl
          (StructureSheaf.toStalkₗ A' (C.homology i) p)) y)))
      simp only [Functor.map_comp, ModuleCat.comp_apply]
      rfl


/-- The canonical target coordinate commutes with stalk localization.
Source: Stacks Project, Tags 01I9, 01HV and 0DJ8.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates).
Proof: expand the target coordinate into exact tilde homology, the termwise
pullback comparison, the inverse derived counit and e. For the sheaf isomorphism
d so obtained, the tilde/global-sections unit followed by the tilde/Gamma counit
is the identity by the adjunction triangle. Naturality of the localization germ
map identifies the localization of Gamma(d) with the stalk of tilde(Gamma(d)).
Composing with the stalk counit therefore gives the stalk of d. The first factors
of d are exactly the isomorphisms defining affineTensorPullbackHomologyStalkIso;
its final factor is the inverse derived counit followed by derived pullback of e.
Functoriality of homology and stalks gives the displayed equation. The argument
works in every degree for arbitrary complexes; zero complexes and identity maps
cause no exceptions, and zero rings have no primes. -/
theorem affineTensorPullbackHomologyStalkIso_coordinates
    (A A' : Type u) [CommRing A] [CommRing A'] (φg' : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
    (p : PrimeSpectrum A') :
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
      Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φg'))
    letI : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w}
      (Spec.map (CommRingCat.ofHom φg'))
    let c :=
      (DerivedCategory.quotientCompQhIso.{w} _).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
      inv ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map
        ((DerivedCategory.quotientCompQhIso _).hom.app P)
    let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
    ∀ y, affineDerivedCohomologyStalkIso A' i p L
        (LocalizedModule.map p.asIdeal.primeCompl b.hom.hom y) =
      s.map (H.map (c ≫
        (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map e.hom))
        (affineTensorPullbackHomologyStalkIso A A' φg' M p i y) := by
  dsimp only
  intro y
  rw [affineTensorPullbackHomologyStalkIso_counit_coordinate A A' φg' K hL M e hc i p y]
  simp only [Functor.map_comp]
  rfl

end AlgebraicGeometry
