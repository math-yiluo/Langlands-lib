/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Extension of a supported perfect object from an affine open

Source: Stacks Project, Tags 08DP, 08DF and 0A9A.
(blueprint: lem-pc-supported-open-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A perfect quasi-coherent object supported on a globally closed subset of an affine
open has a perfect quasi-coherent extension with the extension-by-zero Hom formula.
Source: Stacks Project, Tags 08DP, 08DF and 0A9A, supported Koszul construction.
(blueprint: lem-pc-supported-open-extension).

Proof: Take exact extension by zero along V, after the inverse of Modules.overEquiv V,
and derive this exact composite termwise. Call its value on B A. The derived adjunction
with open restriction gives Hom(A[n], C) = Hom(B[n], C|V), since the exact functor
commutes with shifts. Because B is supported on the globally closed S contained in V,
the canonical map from extension by zero to derived direct image is an isomorphism
(Tags 08DP and 08DF). Supported open pushforward makes A perfect. The affine inclusion
in a quasi-separated scheme is quasi-compact and separated, so derived direct image
has quasi-coherent cohomology (Tag 08D5). At a point of V, the cohomology stalk of A
is that of B; at a point outside V it is zero by exact extension by zero. Thus every
cohomology stalk outside S is zero. The argument works for empty V or S, and for V=X.
There is no zero-detection assertion here: B is arbitrary, and C need not be supported
or quasi-coherent. -/
theorem supported_open_extension
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (V : X.affineOpens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (V : X.Opens).toScheme.toRingedSpace))]
    [∀ U : (V : X.Opens).toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (V : X.Opens).toScheme.toRingedSpace).over U))]
    (S : Set X) (hS : IsClosed S) (hSV : S ⊆ (V : X.Opens))
    (B : schemeDerivedQCohCategory (V : X.Opens).toScheme)
    (hB : Scheme.IsPerfect (V : X.Opens).toScheme B.obj)
    (hsB : ∀ (n : ℤ) (x : (V : X.Opens).toScheme), x.val ∉ S →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (V : X.Opens).toScheme.toRingedSpace)) n).obj
          B.obj).val.presheaf x))) :
    ∃ A : schemeDerivedQCohCategory X, Scheme.IsPerfect X A.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ S →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj A.obj).val.presheaf x))) ∧
      ∀ (C : schemeDerivedCategory X) (n : ℤ),
        Nonempty ((A.obj⟦n⟧ ⟶ C) ≃
          (B.obj⟦n⟧ ⟶
            (schemeOpenRestriction X (V : X.Opens)).mapDerivedCategory.obj C)) := by
  classical
  let O := (V : X.Opens)
  let Y := O.toScheme
  let : IsAffine Y := V.property
  let E := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) O ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) O
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O) ≌
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Scheme.Modules.overEquiv O
  obtain ⟨hRlim, hRcolim, hElim, hEcolim, ⟨adjE⟩⟩ :=
    open_restriction_adjunction_exact X.toRingedSpace O
  let : PreservesFiniteLimits E := hElim
  let : PreservesFiniteColimits E := hEcolim
  let L := e.inverse ⋙ E
  let : PreservesFiniteLimits L := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits L := comp_preservesFiniteColimits _ _
  let : L.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let adj : L ⊣ schemeOpenRestriction X O := e.symm.toAdjunction.comp adjE
  let adjD : L.mapDerivedCategory ⊣ (schemeOpenRestriction X O).mapDerivedCategory :=
    adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (schemeOpenRestriction X O).rightDerivedFunctorIsoMapDerivedCategory
  obtain ⟨er⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace O
  let lr : L ⋙ (schemeOpenRestriction X O) ≅ 𝟭 _ :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.inverse ((Functor.associator E R e.functor).symm ≪≫
        Functor.isoWhiskerRight er e.functor ≪≫ Functor.leftUnitor e.functor) ≪≫
      e.counitIso
  let lrD : L.mapDerivedCategory ⋙ (schemeOpenRestriction X O).mapDerivedCategory ≅
      𝟭 _ := Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso lr ≪≫ Functor.mapDerivedCategoryIdIso _
  have hff := adjD.fullyFaithfulLOfCompIsoId lrD
  let : L.mapDerivedCategory.Full := hff.full
  let : L.mapDerivedCategory.Faithful := hff.faithful
  have : IsIso adjD.unit := by infer_instance
  let adjR0 : schemeOpenRestriction X O ⊣
      RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom :=
    (Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv O).symm
  let adjR : (schemeOpenRestriction X O).mapDerivedCategory ⊣ schemeDerivedDirectImage O.ι :=
    adjR0.mapDerivedCategoryRightDerivedAdjunction
  let φ : L.mapDerivedCategory.obj B.obj ⟶ (schemeDerivedDirectImage O.ι).obj B.obj :=
    adjR.homEquiv _ _ ((asIso (adjD.unit.app B.obj)).inv)
  have hφ : IsIso φ := (Scheme.supported_open_pushforward X O S hS hSV).2.2
    adjR L.mapDerivedCategory adjD B.obj hB hsB φ (by
      change adjD.unit.app B.obj ≫ _ = _
      rw [Equiv.symm_apply_apply]
      exact IsIso.hom_inv_id _)
  let i : L.mapDerivedCategory.obj B.obj ≅ (schemeDerivedDirectImage O.ι).obj B.obj := asIso φ
  have hq : schemeDerivedQCohProperty X (L.mapDerivedCategory.obj B.obj) := by
    have hq' := schemeDerivedDirectImage_preserves_QCoh O.ι B.obj B.property
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor _ n).mapIso i).symm) (hq' n)
  let A : schemeDerivedQCohCategory X := ⟨L.mapDerivedCategory.obj B.obj, hq⟩
  have hp : Scheme.IsPerfect X A.obj := by
    have hp' := (Scheme.supported_open_pushforward X O S hS hSV).1 B.obj hB hsB
    intro x
    obtain ⟨W, hxW, K, hK, ⟨iK⟩⟩ := hp' x
    exact ⟨W, hxW, K, hK, ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) W).mapDerivedCategory.mapIso i ≪≫ iK⟩⟩
  refine ⟨A, hp, ?_, ?_⟩
  · intro n x hx
    let M := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj B.obj
    let H := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x
    let ih := H.mapIso ((L.mapDerivedCategoryHomologyFunctorIso n).symm.app B.obj)
    have hz : Subsingleton (↑(TopCat.Presheaf.stalk (L.obj M).val.presheaf x)) := by
      by_cases hxV : x ∈ O
      · let h := Scheme.Modules.toPresheaf Y ⋙
          TopCat.Presheaf.stalkFunctor _ (⟨x, hxV⟩ : Y)
        let j := (h.mapIso (lr.app M)).symm ≪≫
          h.mapIso ((Scheme.Modules.overFunctorEquiv O).app (L.obj M)) ≪≫
          (Scheme.Modules.restrictStalkNatIso O.ι ⟨x, hxV⟩).app (L.obj M)
        have hs : Subsingleton (↑(TopCat.Presheaf.stalk M.val.presheaf
            (⟨x, hxV⟩ : Y))) := hsB n ⟨x, hxV⟩ hx
        exact j.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp hs
      · exact ModuleCat.isZero_iff_subsingleton.mp
          (moduleExtensionByZero_stalk_outside X.toRingedSpace O (e.inverse.obj M) x hxV)
    exact ih.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr hz
  · intro C n
    exact ⟨(Iso.homCongr ((L.mapDerivedCategory.commShiftIso n).app B.obj).symm
      (Iso.refl C)).trans (adjD.homEquiv (B.obj⟦n⟧) C)⟩

end AlgebraicGeometry
