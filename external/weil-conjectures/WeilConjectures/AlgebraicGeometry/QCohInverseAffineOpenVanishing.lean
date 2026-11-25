/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Topology.OpenModuleCohomology

import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.Topology.ModuleCohomologyTopComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Quasi-coherent vanishing over inverse images of affine opens

Source: Stacks Project, Tags 08D4 (3), 08D5 and 01F4 (2).
(blueprint: new-qcoh-inverse-affine-open-vanishing).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restricting an injective module resolution identifies sections on an open with
module cohomology of the induced open scheme after forgetting global scalars. -/
private theorem open_cohomology_restrict_iso (X : Scheme.{u}) (F : X.Modules)
    (U : X.Opens) (p : ℕ) :
    Nonempty ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F ≅
      (forget₂ (ModuleCat.{u}
        ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat).obj
        ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj F))) := by
  let G := (Scheme.Modules.restrictFunctor U.ι).obj F
  let Y := U.toScheme
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives Y.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
  let I := injectiveResolution F
  let R := Scheme.Modules.restrictFunctor U.ι
  let : R.Additive := ⟨rfl⟩
  let E := (Scheme.Modules.overEquiv U).functor
  let O := SheafOfModules.overFunctor X.ringCatSheaf U
  let eR := Scheme.Modules.overFunctorEquiv U
  obtain ⟨hlim, hcolim, _⟩ := open_restriction_adjunction_exact X.toRingedSpace U
  let : CategoryTheory.Limits.PreservesFiniteLimits O := hlim
  let : CategoryTheory.Limits.PreservesFiniteColimits O := hcolim
  let : CategoryTheory.Limits.PreservesFiniteLimits R :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso eR
  let : CategoryTheory.Limits.PreservesFiniteColimits R :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso eR
  have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
    have h := (RingedSpace.restrict_injectiveResolution X.toRingedSpace U F I).2 n
    exact Injective.of_iso (eR.app (I.cocomplex.X n))
      (E.injective_obj_of_injective h)
  let e₀ := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).app F
  let J : InjectiveResolution G :=
    { cocomplex := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      injective := hinj
      ι := e₀.inv ≫ (R.mapHomologicalComplex (.up ℕ)).map I.ι
      quasiIso := by infer_instance }
  let Q := forget₂ (ModuleCat.{u}
    ((moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat
  let S := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let T := RingedSpace.openModuleSections X.toRingedSpace U
  let : S.Additive := RingedSpace.globalSectionsFunctor_additive Y.toRingedSpace
  let : Q.Additive := inferInstance
  let : T.Additive := RingedSpace.openModuleSections_additive X.toRingedSpace U
  let eSections : T ≅ R ⋙ S ⋙ Q :=
    NatIso.ofComponents (fun (M : X.Modules) ↦ by
      change Γ(M, U) ≅ Γ(Scheme.Modules.restrict M U.ι, ⊤)
      exact ((Scheme.Modules.toPresheaf X).obj M |>.mapIso (eqToIso (by simp)).op) ≪≫
        (Scheme.Modules.restrictAppIso U.ι M ⊤).symm)
      (by
        intro M N f
        change ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op U) ≫
            ((Scheme.Modules.toPresheaf X).obj N).map (eqToHom (by simp : U.ι ''ᵁ ⊤ = U)).op =
          ((Scheme.Modules.toPresheaf X).obj M).map (eqToHom (by simp : U.ι ''ᵁ ⊤ = U)).op ≫
            ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op (U.ι ''ᵁ ⊤))
        exact ((Scheme.Modules.toPresheaf X).map f).naturality _ |>.symm)
  let eComplex := (NatIso.mapHomologicalComplex eSections (.up ℕ)).app I.cocomplex
  let K := (S.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let eHomology := (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) p).mapIso
    eComplex
  let eForget := (K.sc p).mapHomologyIso Q
  exact ⟨I.isoRightDerivedObj T p ≪≫ eHomology ≪≫ eForget ≪≫
    Q.mapIso (J.isoRightDerivedObj S p).symm⟩

/-- Positive module cohomology vanishes on inverse images of affine opens
when higher direct image vanishes on quasi-coherent modules.
Source: Stacks Project, Tags 08D5, 01F4 (2), 01XJ and 01XB.
(blueprint: new-qcoh-inverse-affine-open-vanishing).

Proof:
1. Put U = f inverse-image V. The restriction F|U is quasi-coherent.
Restriction of an injective resolution remains injective, so the cohomology
in the conclusion computes H^p(U,F|U).
2. The bounded-below/unbounded single-object comparison identifies
H^p(Rf_*(F[0])) with ordinary R^p f_*F, which is zero by hacyc.
Restrict an injective resolution of F to U. The sectionwise pushforward/restriction
comparison identifies g_*(I|U) with (f_*I)|V, where g = f|V.
Exact restriction on Y commutes with homology, so R^p g_*(F|U) is zero.
All R^q g_*(F|U) are quasi-coherent by the existing isQuasicoherent_higherDirectImage
statement (Stacks 01XJ (1)); only qcqs is needed, with no uniform support bound.
3. Since V is affine, affine vanishing kills positive cohomology of each
of these quasi-coherent higher direct images. The canonical Leray edge
is consequently an isomorphism. In degree p > 0 its target is sections
of the zero higher direct image from step 2. The source, and hence the
stated open module cohomology, is zero. The empty affine open gives the
zero sections complex, so is included without an extra hypothesis. -/
theorem qcoh_acyclic_inverse_affine_open_vanishing {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (V : Y.Opens) (hV : IsAffineOpen V)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : F.IsQuasicoherent) (p : ℕ) (hp : 0 < p) :
    IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p (f ⁻¹ᵁ V)).obj F) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let U := f ⁻¹ᵁ V
  let g := f ∣_ V
  let G := (Scheme.Modules.restrictFunctor U.ι).obj F
  let : F.IsQuasicoherent := hF
  let : IsAffine V.toScheme := hV
  let : EnoughInjectives U.toScheme.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives U.toScheme.toRingedSpace).2
  let : EnoughInjectives V.toScheme.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives V.toScheme.toRingedSpace).2
  have hzero : IsZero
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F) := by
    exact (hacyc F hF p (by exact_mod_cast hp)).of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F p).symm
  have hrestrict (q : ℕ) : Nonempty
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived q).obj G ≅
        (Scheme.Modules.restrictFunctor V.ι).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F)) := by
    -- Derive the sectionwise comparison using the restricted injective resolution.
    let R := Scheme.Modules.restrictFunctor U.ι
    let B := Scheme.Modules.restrictFunctor V.ι
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let D' := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let : D.Additive := RingedSpace.moduleDirectImage_additive _
    let : D'.Additive := RingedSpace.moduleDirectImage_additive _
    let : R.Additive := ⟨rfl⟩
    let : B.Additive := ⟨rfl⟩
    let O := SheafOfModules.overFunctor X.ringCatSheaf U
    let eR := Scheme.Modules.overFunctorEquiv U
    obtain ⟨hlim, hcolim, _⟩ := open_restriction_adjunction_exact X.toRingedSpace U
    let : PreservesFiniteLimits O := hlim
    let : PreservesFiniteColimits O := hcolim
    let : PreservesFiniteLimits R := preservesFiniteLimits_of_natIso eR
    let : PreservesFiniteColimits R := preservesFiniteColimits_of_natIso eR
    let OY := SheafOfModules.overFunctor Y.ringCatSheaf V
    let eB := Scheme.Modules.overFunctorEquiv V
    obtain ⟨hlimY, hcolimY, _⟩ := open_restriction_adjunction_exact Y.toRingedSpace V
    let : PreservesFiniteLimits OY := hlimY
    let : PreservesFiniteColimits OY := hcolimY
    let : PreservesFiniteLimits B := preservesFiniteLimits_of_natIso eB
    let : PreservesFiniteColimits B := preservesFiniteColimits_of_natIso eB
    let I := injectiveResolution F
    have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
      have h := (RingedSpace.restrict_injectiveResolution X.toRingedSpace U F I).2 n
      exact Injective.of_iso (eR.app (I.cocomplex.X n))
        ((Scheme.Modules.overEquiv U).functor.injective_obj_of_injective h)
    let J : InjectiveResolution G :=
      { cocomplex := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
        injective := hinj
        ι := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).inv.app F ≫
          (R.mapHomologicalComplex (.up ℕ)).map I.ι
        quasiIso := by infer_instance }
    -- The image of an open of V under g agrees with its inverse image under f.
    let e : D ⋙ B ≅ R ⋙ D' := by
      change Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
        Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward g
      refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
        (SheafOfModules.pushforwardComp _ _).symm
      refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
      · refine NatIso.ofComponents (fun W ↦ eqToIso ?_) ?_
        · exact image_morphismRestrict_preimage f V W
        · cat_disch
      · ext W x
        simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
        dsimp
        exact congr($(morphismRestrict_app f V W.unop) x).symm
    let K := (D.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    let eK := (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I.cocomplex ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ D'))
        (.up ℕ)).symm.app I.cocomplex
    exact ⟨J.isoRightDerivedObj D' q ≪≫
      (HomologicalComplex.homologyFunctor V.toScheme.Modules (.up ℕ) q).mapIso eK.symm ≪≫
      (K.sc q).mapHomologyIso B ≪≫ B.mapIso (I.isoRightDerivedObj D q).symm⟩
  obtain ⟨ε, _, hε⟩ := exists_lerayEdge_isIso_of_vanishing g
  have hvan (q r : ℕ) (hr : 0 < r) :
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived q).obj G)) := by
    let M := ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived q).obj G
    have : M.IsQuasicoherent := Scheme.Modules.isQuasicoherent_higherDirectImage g G q
    have : Subsingleton ((RingedSpace.openModuleCohomology V.toScheme.toRingedSpace r ⊤).obj
        M) := subsingleton_openModuleCohomology_of_isAffineOpen V.toScheme M ⊤
          (isAffineOpen_top _) r hr
    obtain ⟨e⟩ := RingedSpace.nonempty_moduleCohomology_top_iso V.toScheme.toRingedSpace r
    have hz := (AddCommGrpCat.isZero_of_subsingleton _).of_iso (e.app M)
    have : Subsingleton ((forget₂ (ModuleCat.{u}
        ((moduleRings V.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat).obj
          ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj M)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp hz
    exact ModuleCat.isZero_of_subsingleton _
  have : IsIso ((ε p).app G) := hε G hvan p
  obtain ⟨eR⟩ := hrestrict p
  have hzR : IsZero
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived p).obj G) :=
    ((Scheme.Modules.restrictFunctor V.ι).map_isZero hzero).of_iso eR
  have hzS := (RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat).map_isZero hzR
  have hzH := hzS.of_iso (asIso ((ε p).app G))
  obtain ⟨eO⟩ := open_cohomology_restrict_iso X F U p
  exact hzH.of_iso eO

end AlgebraicGeometry
