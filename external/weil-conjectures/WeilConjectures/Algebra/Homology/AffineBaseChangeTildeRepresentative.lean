/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization


public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization

/-! # AffineBaseChangeTildeRepresentative

Source: Stacks Project, Tag 0DJ8.
(blueprint: def-pc-affine-base-change-tilde-representative-iso). -/

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

/-- The unit-normalized tensor/tilde comparison on complexes, shared by the
pullback representative and calculations with it. Source: Stacks, Tags 01I9 and 08DW.
(blueprint: def-pc-affine-base-change-tilde-representative-iso). -/
def affineBaseChangeTildeComplexIso
    (A D : Type u) [CommRing A] [CommRing D] (φ : A →+* D)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))
    let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} _
    (E.mapHomologicalComplex (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M) ≅
      ((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) := by
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
    Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} _
  let : (affinePushforwardTilde A).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : (affinePushforwardTilde D).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of D) f g
  let θ : affinePushforwardTilde A ⋙ E ≅
      ModuleCat.extendScalars φ ⋙ affinePushforwardTilde D :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))
  exact (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app M

/-- Degreewise formula for the complex comparison.
Source: Stacks, Tag 01I9; this is the defining termwise action of the comparison. 
(blueprint: def-pc-affine-base-change-tilde-representative-iso)
-/
theorem affineBaseChangeTildeComplexIso_hom_f
    (A D : Type u) [CommRing A] [CommRing D] (φ : A →+* D)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (affineBaseChangeTildeComplexIso A D φ M).hom.f i =
      (Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
        (CommRingCat.ofHom φ))).hom.app (M.X i) := by
  rfl

/-- The actual tilde representative of affine derived pullback.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: def-pc-affine-base-change-tilde-representative-iso).
The tensor-pullback comparison is unit-normalized. The other two factors are
respectively the inverse of the supplied derived counit and the image of e. -/
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affinePushforwardTilde A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let P := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M
  let : IsIso ((SingleComplexBaseChange.counit f).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc
  let δ := affineBaseChangeTildeComplexIso A A' φ M
  exact (DerivedCategory.Q.mapIso δ).symm ≪≫
    (cast (by rfl) (asIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm) ≪≫
    (derivedPullback f).mapIso e


/-- Cancelling the supplied pullback counit leaves exactly the inverse complex
comparison. Source: Stacks, Tags 01I9 and 08HY. The representative has three factors:
the inverse comparison, the inverse counit, and the image of the identity. Functoriality
removes the last factor and the middle factor cancels against the counit. 
(blueprint: def-pc-affine-base-change-tilde-representative-iso)
-/
theorem affineBaseChangeTildeRepresentativeIso_counit
    (A D : Type u) [CommRing A] [CommRing D] (φ : A →+* D)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    (affineBaseChangeTildeRepresentativeIso A D φ
      (DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)) M
      (Iso.refl _) hc).hom ≫
      cast (by rfl) ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M))) =
      DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv := by
  let p := Spec.map (CommRingCat.ofHom φ)
  let P := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M
  let c := (SingleComplexBaseChange.counit p).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let : IsIso c := hc
  dsimp only [affineBaseChangeTildeRepresentativeIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.refl_hom, Category.assoc]
  change DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv ≫
    inv c ≫ (derivedPullback p).map (𝟙 _) ≫ c = _
  erw [(derivedPullback p).map_id]
  change DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv ≫
    inv c ≫ 𝟙 _ ≫ c = _
  simp only [Category.id_comp, IsIso.inv_hom_id, Category.comp_id]

/-- The chosen pullback representative is compatible with transport from the identity
representative. Source: Stacks Project, Tag 08HY. This follows directly from its
three defining factors and functoriality of derived pullback. 
(blueprint: def-pc-affine-base-change-tilde-representative-iso)
-/
theorem affineBaseChangeTildeRepresentativeIso_identity_hom
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    (affineBaseChangeTildeRepresentativeIso A A' φ
      (DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)) M
      (Iso.refl _) hc).hom ≫ (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map e.hom =
      (affineBaseChangeTildeRepresentativeIso A A' φ K M e hc).hom := by
  dsimp only [affineBaseChangeTildeRepresentativeIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom,
    Category.assoc]
  congr 1
  congr 1
  exact ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).map_comp
    (𝟙 _) e.hom).symm.trans
      (congrArg (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
        (Category.id_comp e.hom))

end AlgebraicGeometry
