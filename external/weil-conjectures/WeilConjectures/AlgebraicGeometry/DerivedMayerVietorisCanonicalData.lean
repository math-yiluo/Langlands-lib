/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisExact
public import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonIso
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Explicit data for the natural Mayer--Vietoris triangle

Source: Stacks Project, Cohomology, Tags 08BV, 08FE and 0D5T.
(blueprint: def-pc-derived-mayer-vietoris-canonical-data).
The boundary is constructed from the fixed functorial K-injective resolution and the
short-exact-sequence boundary, without choosing a witness of a boundary existence theorem.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

variable (X : Scheme.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The existing abelian structure on modules on a scheme, specialized once.
This named construction avoids repeated searches through the generic sheafification
instances. It is the Mathlib structure, with no choice of new abelian data.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
abbrev schemeMVModuleAbelian (T : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) :
    Abelian (SheafOfModules.{u} R) := inferInstance

attribute [local instance 2000] schemeMVModuleAbelian

/-- Exact derived restriction, with its exactness witnesses elaborated once.
This is an abbreviation for the existing derived restriction functor, not new data.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
abbrev schemeMVDerivedRestriction (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    schemeDerivedCategory X ⥤ schemeDerivedCategory U.toScheme :=
  (schemeOpenRestriction X U).mapDerivedCategory

/-- Derive the fixed underived restriction adjunction.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVAdjunction (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    (schemeMVDerivedRestriction X U) ⊣ schemeDerivedDirectImage U.ι :=
  let a : schemeOpenRestriction X U ⊣
    RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom := schemeOpenModuleAdjunction X U
  a.mapDerivedCategoryRightDerivedAdjunction

/-- The fixed K-injective representative used in the natural boundary construction.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
abbrev schemeMVResolution (E : schemeDerivedCategory X) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  (CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj (DerivedCategory.Q.objPreimage E)

/-- K-injectivity of the fixed functorial resolution.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
instance schemeMVResolution_isKInjective (E : schemeDerivedCategory X) :
    (schemeMVResolution X E).IsKInjective := by
  dsimp only [schemeMVResolution]
  infer_instance

/-- Injectivity of each term of the fixed functorial resolution.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
instance schemeMVResolution_term_injective (E : schemeDerivedCategory X) (n : ℤ) :
    Injective ((schemeMVResolution X E).X n) := by
  dsimp only [schemeMVResolution]
  infer_instance

/-- The inverse localized resolution map followed by the localization preimage comparison.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVResolutionIso (E : schemeDerivedCategory X) :
    DerivedCategory.Q.obj (schemeMVResolution X E) ≅ E := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app
      (DerivedCategory.Q.objPreimage E)) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
  exact (asIso (DerivedCategory.Q.map
    ((CochainComplex.toKInjectiveResolution.{u} A).app
      (DerivedCategory.Q.objPreimage E)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E

/-- Boundary of the concrete short exact sequence, transported to a derived object.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVBoundary (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage (U ⊓ V).ι).obj
      ((schemeMVDerivedRestriction X (U ⊓ V)).obj E) ⟶ E⟦(1 : ℤ)⟧ :=
  let H := (schemeMVDerivedRestriction X (U ⊓ V)) ⋙
    schemeDerivedDirectImage (U ⊓ V).ι
  H.map (schemeMVResolutionIso X E).inv ≫
    ((schemeOpenModuleImageComplexComparison X (U ⊓ V) (schemeMVResolution X E)
      (schemeMVAdjunction X (U ⊓ V))).inv ≫
      DerivedCategory.triangleOfSESδ
        (schemeMayerVietorisComplex_shortExact X U V hcover (schemeMVResolution X E)
          (fun _ ↦ inferInstance))) ≫ (schemeMVResolutionIso X E).hom⟦(1 : ℤ)⟧'

/-- The triangle with the fixed units, restrictions and explicitly constructed boundary.
Source: Stacks Tag 08BV (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVTriangle (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) : Triangle (schemeDerivedCategory X) :=
  Triangle.mk
    (biprod.lift ((schemeMVAdjunction X U).unit.app E)
      ((schemeMVAdjunction X V).unit.app E))
    (biprod.desc (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
      (schemeMVAdjunction X U) (schemeMVAdjunction X (U ⊓ V)) E)
      (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
        (schemeMVAdjunction X V) (schemeMVAdjunction X (U ⊓ V)) E)))
    (schemeMVBoundary X U V hcover E)

variable {X} {Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The existing triangulated structure of derived direct image, specialized once.
Source: Stacks Tag 0D5T (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
abbrev schemeMVDirectImageTriangulated (h : X ⟶ Y) :
    (schemeDerivedDirectImage h).IsTriangulated := inferInstance

attribute [local instance 2000] schemeMVDirectImageTriangulated

/-- The image triangle, with the right-derived shift commutation elaborated once.
Source: Stacks Tag 0DJ9 (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVImageTriangle (h : X ⟶ Y) (T : Triangle (schemeDerivedCategory X)) :
    Triangle (schemeDerivedCategory Y) :=
  (schemeDerivedDirectImage h).mapTriangle.obj T

/-- The constructed image triangle is distinguished when its source is.
Source: Stacks Tag 0DJ9 (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
theorem schemeMVImageTriangle_distinguished (h : X ⟶ Y)
    (T : Triangle (schemeDerivedCategory X))
    (hT : T ∈ distTriang (schemeDerivedCategory X)) :
    schemeMVImageTriangle h T ∈ distTriang (schemeDerivedCategory Y) :=
  (schemeDerivedDirectImage h).map_distinguished T hT

variable
  [∀ T : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  [∀ T : Y.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]

/-- Composition comparison selected by its determining right-derived unit equation.
Source: Stacks Tag 0D5T (blueprint: def-pc-derived-mayer-vietoris-canonical-data).
The equation in exists_derivedModuleDirectImageComposition determines this isomorphism
by the right-derived universal property; this is not a choice of an arbitrary isomorphism. -/
def schemeMVDirectImageComposition {Z : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (p : X ⟶ Y) (f : Y ⟶ Z) :
    schemeDerivedDirectImage (p ≫ f) ≅
      schemeDerivedDirectImage p ⋙ schemeDerivedDirectImage f :=
  (Classical.choose (RingedSpace.exists_derivedModuleDirectImageComposition
    p.toLRSHom.toShHom f.toLRSHom.toShHom)).symm

-- Explicit additivity witnesses require a larger typeclass-search budget.
/-- The derived sectionwise identity comparing direct image and open restriction.
Source: Stacks Tag 08FE (blueprint: def-pc-derived-mayer-vietoris-canonical-data).
This is the explicit construction used in schemeDerivedDirectImage_openRestriction,
retained as data rather than hidden behind Nonempty. -/
def schemeMVOpenRestrictionComparison (f : X ⟶ Y) (V : Y.Opens) :
    schemeDerivedDirectImage f ⋙ (schemeMVDerivedRestriction Y V) ≅
      (schemeMVDerivedRestriction X (f ⁻¹ᵁ V)) ⋙
        schemeDerivedDirectImage (f ∣_ V) := by
  classical
  let rX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ V)
  let eX := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V)))
    (D := SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ V))
  let rY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  let eY := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
    (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv V)
  have : rX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : (rX ⋙ eX).Additive := Functor.additive_of_preserves_binary_products _
  have : (rY ⋙ eY).Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (rX ⋙ eX) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (rX ⋙ eX) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (rY ⋙ eY) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (rY ⋙ eY) := comp_preservesFiniteColimits _ _
  have : rX.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open X.toRingedSpace (f ⁻¹ᵁ V) I⟩
  have : eX.PreservesKInjectiveComplexes := inferInstance
  have : (rX ⋙ eX).PreservesKInjectiveComplexes := inferInstance
  -- The underived comparison is the sectionwise identity from Tag 08FE.
  have e : RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙ (rY ⋙ eY) ≅
      (rX ⋙ eX) ⋙ RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom := by
    refine Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv V) ≪≫
      ?_ ≪≫ Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V)).symm _
    change Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (f ∣_ V)
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
  -- Derive the comparison, using exactness on Y and K-injectivity preservation on X.
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{w, w, w}
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (rY ⋙ eY)).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, w, w} e ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1,
      w, w, w} (rX ⋙ eX)
      (RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom) ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{w, w} (rX ⋙ eX))
      (schemeDerivedDirectImage (f ∣_ V))

/-- Compose the recorded direct-image and open-restriction comparisons.
Source: Stacks Tags 0D5T and 08FE
(blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVOpenComparison (h : X ⟶ Y) (U : Y.Opens) (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj
      ((schemeMVDerivedRestriction X (h ⁻¹ᵁ U)).obj E)) ≅
    (schemeDerivedDirectImage U.ι).obj
      ((schemeMVDerivedRestriction Y U).obj ((schemeDerivedDirectImage h).obj E)) :=
  ((schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
    eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
    schemeMVDirectImageComposition (h ∣_ U) U.ι).app
      ((schemeMVDerivedRestriction X (h ⁻¹ᵁ U)).obj E) ≪≫
    (schemeDerivedDirectImage U.ι).mapIso
      ((schemeMVOpenRestrictionComparison h U).symm.app E)

/-- The biproduct comparison followed by the two open comparisons.
Source: Stacks Tag 0DJ9 (blueprint: def-pc-derived-mayer-vietoris-canonical-data). -/
def schemeMVMiddleComparison (h : X ⟶ Y) (U V : Y.Opens)
    (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage h).obj
      (((schemeMVDerivedRestriction X (h ⁻¹ᵁ U)) ⋙
        schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj E ⊞
       ((schemeMVDerivedRestriction X (h ⁻¹ᵁ V)) ⋙
        schemeDerivedDirectImage (h ⁻¹ᵁ V).ι).obj E) ≅
    (((schemeMVDerivedRestriction Y U) ⋙ schemeDerivedDirectImage U.ι).obj
      ((schemeDerivedDirectImage h).obj E) ⊞
     ((schemeMVDerivedRestriction Y V) ⋙ schemeDerivedDirectImage V.ι).obj
      ((schemeDerivedDirectImage h).obj E)) :=
  have : (schemeDerivedDirectImage h).Additive := inferInstance
  have : PreservesBinaryBiproducts (schemeDerivedDirectImage h) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  (schemeDerivedDirectImage h).mapBiprod _ _ ≪≫
    biprod.mapIso (schemeMVOpenComparison h U E) (schemeMVOpenComparison h V E)

end AlgebraicGeometry
