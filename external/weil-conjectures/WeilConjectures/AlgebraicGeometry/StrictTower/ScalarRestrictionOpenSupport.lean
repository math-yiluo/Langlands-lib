/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import Mathlib.CategoryTheory.Adjunction.Triple

/-! # Scalar restriction preserves ordinary open support

Source: Stacks Project, Modules on Sites, Tag 03DI, the sheafified direct-sum
construction of extension by zero (blueprint: lem-sf-scalar-restriction-open-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

set_option backward.defeqAttrib.useBackward true

/-- Descend the restricted sheafification unit; its underlying additive map is identity. -/
private def scalarSheafificationIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}}
    (a : R ⟶ S) (P : PresheafOfModules.{u + 1} S.obj) :
    (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)).obj
        ((PresheafOfModules.restrictScalars a.hom).obj P) ≅
      (SheafOfModules.restrictScalars a).obj
        ((PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)).obj P) := by
  let Q := (PresheafOfModules.restrictScalars a.hom).obj P
  let F := (SheafOfModules.restrictScalars a).obj
    ((PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)).obj P)
  let g : Q ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj F.val :=
    (PresheafOfModules.restrictScalars a.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 S.obj)).unit.app P)
  let f : (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)).obj Q ⟶ F :=
    (PresheafOfModules.sheafificationHomEquiv.{u + 1} (𝟙 R.obj)).symm g
  have hf : (SheafOfModules.toSheaf R).map f = 𝟙 _ := by
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    rfl
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by rw [hf]; infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact asIso f

/-- Identity on the direct sums intertwines scalar restriction and extension. -/
private def scalarExtensionPresheafIso
    {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}}
    (a : R ⟶ S) (U : C) (M : SheafOfModules.{u + 1} (S.over U)) :
    SheafOfModules.extensionByZeroPresheafObj.{u + 1} R U
        ((SheafOfModules.restrictScalars ((J.overPullback RingCat U).map a)).obj M) ≅
      (PresheafOfModules.restrictScalars a.hom).obj
        (SheafOfModules.extensionByZeroPresheafObj.{u + 1} S U M) := by
  let Q := SheafOfModules.extensionByZeroPresheafObj.{u + 1} R U
    ((SheafOfModules.restrictScalars ((J.overPullback RingCat U).map a)).obj M)
  let P := (PresheafOfModules.restrictScalars a.hom).obj
    (SheafOfModules.extensionByZeroPresheafObj.{u + 1} S U M)
  let f : Q ⟶ P := PresheafOfModules.homMk (𝟙 Q.presheaf) (fun _ _ _ => by rfl)
  have : IsIso ((PresheafOfModules.toPresheaf R.obj).map f) :=
    show IsIso (𝟙 _) from inferInstance
  have : IsIso f := isIso_of_reflects_iso f (PresheafOfModules.toPresheaf R.obj)
  exact asIso f

/-- Subterminal localization has invertible unit, by the restriction adjunction triple. -/
private theorem localizedOpen_unit_isIso
    {X : Scheme.{u}} (U : X.ProEt) [IsOpenImmersion U.hom]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    IsIso (SheafOfModules.localizedModuleAdjunctionIndependent R U).unit := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let b := SheafOfModules.overPushforwardOverAdj (R := A) U
  have hsub : ∀ W : X.ProEt, Subsingleton (W ⟶ U) := by
    intro W
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact f.w.trans g.w.symm
  have : (Over.forget U).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (@Subsingleton.elim _ (hsub V.left) _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    change IsIso (N.val.presheaf.map ((Over.forgetAdjStar U).unit.app W.unop).op)
    infer_instance
  let triple : Adjunction.Triple _ _ _ :=
    ⟨SheafOfModules.localizedModuleAdjunctionIndependent R U, b⟩
  exact triple.isIso_unit_iff_isIso_counit.mpr inferInstance

/-- Restricting a single constant coefficient action preserves open support.

Source: Stacks Project, sites-modules.tex, Tag 03DI (lemma-extension-by-zero),
using Tag 03CY (lemma-sheafification-presheaf-modules)
(blueprint: lem-sf-scalar-restriction-open-support).

Proof: identify the small pro-etale site of U with the site localized at the
subterminal open j. The specified module pullback is restriction in these coordinates;
adjoint uniqueness identifies its chosen left adjoint with localized extension by zero.
For a localized A-module M, the extension presheaf at H is the direct sum of M(H -> U)
over lifts H -> U. Restrict the action on each summand through a. The two resulting
presheaves have the same underlying additive groups, restrictions, and B-actions.
Identity on each summand therefore identifies restriction of the A-extension
presheaf with the B-extension presheaf of the restricted localized module. The same
identity extends to sheafification: restriction changes only the action, and the
underlying additive sheafification is unchanged. Thus the restricted extension lies
in the essential image of the chosen B-extension. Its B-open counit is invertible,
since open extension is fully faithful. The argument includes the empty open, where
both extension presheaves are zero, and the identity open, where restriction is the
identity. It assumes no flatness of a. -/
theorem restrictScalars_openCounit_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {U X : Scheme.{u}} (a : coefficients B X ⟶ coefficients A X)
    (j : U ⟶ X) [IsOpenImmersion j] (M : Modules A U) :
    IsIso ((moduleJAdj.{u} B j).counit.app
      ((Scheme.proEtaleRingRestrictScalars a).obj
        ((moduleJ.{u} A j).obj M))) := by
  obtain ⟨eA, ⟨hA⟩⟩ := Scheme.proEtaleOpen_slicePresentation j
    (coefficients A X) (coefficients A U) (constantRingIso A j)
  obtain ⟨eB, ⟨hB⟩⟩ := Scheme.proEtaleOpen_slicePresentation j
    (coefficients B X) (coefficients B U) (constantRingIso B j)
  let RB := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
  let RA := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients A X)
  let ar : RB ⟶ RA := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a
  let W := Scheme.ProEt.mk j
  have : IsOpenImmersion W.hom := inferInstanceAs (IsOpenImmersion j)
  let N := (SheafOfModules.restrictScalars
    (((Scheme.ProEt.topology X).overPullback RingCat W).map ar)).obj (eA.functor.obj M)
  have : IsIso (SheafOfModules.localizedModuleAdjunctionIndependent
      (coefficients B X) W).unit := localizedOpen_unit_isIso W (coefficients B X)
  let ff := (SheafOfModules.localizedModuleAdjunctionIndependent
    (coefficients B X) W).fullyFaithfulLOfIsIsoUnit
  let ffB := ((Functor.FullyFaithful.ofFullyFaithful eB.functor).comp ff).ofIso hB.symm
  have : (moduleJ B j).Full := ffB.full
  have : (moduleJ B j).Faithful := ffB.faithful
  let q := (PresheafOfModules.sheafification.{u + 1} (𝟙 RB.obj)).mapIso
    (scalarExtensionPresheafIso ar W (eA.functor.obj M)) ≪≫
      scalarSheafificationIso ar
        (SheafOfModules.extensionByZeroPresheafObj.{u + 1} RA W (eA.functor.obj M))
  let t : (Scheme.proEtaleRingRestrictScalars a).obj ((moduleJ A j).obj M) ≅
      (moduleJ B j).obj (eB.inverse.obj N) :=
    (Scheme.proEtaleRingRestrictScalars a).mapIso (hA.app M) ≪≫ q.symm ≪≫
      (SheafOfModules.localizedModuleExtension (coefficients B X) W).mapIso
        (eB.counitIso.app N).symm ≪≫ (hB.app (eB.inverse.obj N)).symm
  exact (moduleJAdj B j).isIso_counit_app_of_iso t

end AlgebraicGeometry.ProEtale.StrictTower
