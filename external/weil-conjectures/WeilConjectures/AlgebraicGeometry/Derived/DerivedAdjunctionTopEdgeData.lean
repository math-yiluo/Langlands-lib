/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackTopCohomology
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
public import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Whiskering

/-! # Canonical local models and the truncated-counit edge

The existing resolution, local-class, Leray and pullback-inverse constructions retain
exactly their original names and terms. The truncated-counit edge uses the adjoint of
the upper-truncation inclusion and its invertible map on top cohomology. Keeping the
constructions here lets a local calculation import them without importing its consumer.

Source: Stacks Project, cohomology.tex, Tags 0BKJ, 0D5X and 079W; derived.tex,
Tags 08J5 and 06XS (blueprint: def-weil-pbc-truncated-counit-edge).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry

namespace RingedSpace

variable (X : RingedSpace.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]

/-- A fixed K-injective representative, using the published functorial resolution.
Source: Stacks, Tag 079V (blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
abbrev topEdgeResolution (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :=
  (CochainComplex.kInjectiveResolutionFunctor.{u} (SheafOfModules.{u} (moduleRings X))).obj
    (DerivedCategory.Q.objPreimage K)

/-- The canonical identification of that representative with K, induced by the resolution
quasi-isomorphism. Source: Stacks, Tag 079V
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeResolutionIso (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    DerivedCategory.Q.obj (topEdgeResolution X K) ≅ K :=
  let r := (CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings X))).app (DerivedCategory.Q.objPreimage K)
  letI : QuasiIso r :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ _).2
  (asIso (DerivedCategory.Q.map r)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K

/-- H^q of local sections computed on the fixed representative. Both isomorphisms are
canonical derived-unit comparisons. Source: Stacks, Tags 0BKJ and 0D5W
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeLocalModel (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (localHypercohomologyPresheaf X q).obj K ≅
      (((localAbelianSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (topEdgeResolution X K)).homology q :=
  (localHypercohomologyPresheaf X q).mapIso (topEdgeResolutionIso X K).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((localAbelianSections X).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (localSectionsEnoughKInjectives X) (𝟙 (topEdgeResolution X K))) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- The canonical local-class map Θ, namely the abelian sheafification unit followed by
its fixed cohomology-sheaf identification. Source: Stacks, Tag 0BKJ
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeLocalClass (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (localHypercohomologyPresheaf X q).obj K ⟶
      (localAbelianSections X).obj ((DerivedCategory.homologyFunctor _ q).obj K) :=
  (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app _ ≫
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (localHypercohomologySheafificationAt q K).hom

variable {X} {Y : RingedSpace.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]

/-- Transport between the two published right-derived direct images, by comparing both
units on the same K-injective representative. Source: Stacks, Tags 079V and 0D5W
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeDirectImageComparison (g : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (sectionDerivedDirectImage g).obj K ≅ (derivedModuleDirectImage g).obj K :=
  (sectionDerivedDirectImage g).mapIso (topEdgeResolutionIso X K).symm ≪≫
    (moduleDirectImage g).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (localSectionsEnoughKInjectives X) (𝟙 (topEdgeResolution X K)) ≪≫
    ((derivedModuleDirectImage g).mapIso (topEdgeResolutionIso X K).symm ≪≫
      (moduleDirectImage g).rightDerivedFunctorObjQIso (topEdgeResolution X K)).symm

/-- The inverse-open local cohomology presheaf computed on the same representative.
Source: Stacks, Tag 0D5X (blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeInverseModel (g : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (inverseOpenHypercohomologyPresheaf g q).obj K ≅
      ((((moduleDirectImage g ⋙ localAbelianSections Y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (topEdgeResolution X K)).homology q) :=
  (inverseOpenHypercohomologyPresheaf g q).mapIso (topEdgeResolutionIso X K).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((moduleDirectImage g ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (localSectionsEnoughKInjectives X) (𝟙 (topEdgeResolution X K))) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- The local derived-sections isomorphism λ, in the direction used by the edge.
The selected presheaf isomorphism is uniquely fixed by its stated hom transformation.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeLocalLeray (g : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (localHypercohomologyPresheaf Y q).obj ((derivedModuleDirectImage g).obj K) ≅
      (inverseOpenHypercohomologyPresheaf g q).obj K :=
  (localHypercohomologyPresheaf Y q).mapIso (topEdgeDirectImageComparison g K).symm ≪≫
    (Classical.choose (unboundedDirectImage_sectionPresheaf g q)).symm.app K

/-- Θ on inverse-image opens. Exact precomposition commutes with homology; the two
model comparisons then identify H^q(g^-1 V,K) with the corresponding local sections of K.
Source: Stacks, Tags 0BKJ and 0D5X
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeInverseLocalClass (g : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (inverseOpenHypercohomologyPresheaf g q).obj K ⟶
      (localAbelianSections Y).obj
        ((moduleDirectImage g).obj ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  (topEdgeInverseModel g q K).hom ≫
    (((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opens.map g.hom.base).op).mapHomologicalComplexHomologyIso
        (ComplexShape.up ℤ) q).hom.app
          (((localAbelianSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (topEdgeResolution X K)) ≫
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opens.map g.hom.base).op).map
        ((topEdgeLocalModel X q K).inv ≫ topEdgeLocalClass X q K)

end RingedSpace

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The inverse of the already recorded canonical top comparison κ.
Source: Stacks, Tag 05TC (blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgePullbackInverse {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE q) :=
  letI := (derivedPullback_topCohomology g q C hC).choose_spec.2.1
  inv (derivedPullbackTopCohomology g q C hC)

/-- The edge obtained by transposing the inclusion of the upper truncation of Rg_*K.
The inverse on cohomology exists because upper truncation preserves degree q.
Source: Stacks, derived.tex, Tags 08J5 and 05TC; cohomology.tex, Tag 079W
(blueprint: def-weil-pbc-truncated-counit-edge). -/
def topEdgeTruncatedCounit {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (K : schemeDerivedCategory T) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj
        ((schemeDerivedDirectImage g).obj K) ⟶
      (Scheme.Modules.pushforward g).obj
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj K) :=
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let P := (t.truncLE q).obj ((schemeDerivedDirectImage g).obj K)
  let i := (t.truncLEι q).app ((schemeDerivedDirectImage g).obj K)
  let d := (@pinnedDerivedAdjunction.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f)
    _ _ g).homEquiv P K |>.symm <| i
  let H := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  letI : IsIso (H.map i) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (q + 1) q (by omega)
  inv (H.map i) ≫
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv _ _
      (topEdgePullbackInverse g q P (by infer_instance) ≫
        (DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map d)

end AlgebraicGeometry
