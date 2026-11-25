/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeAffineChartComparison
import WeilConjectures.AlgebraicGeometry.FlatOverAffineOpenRestriction

/-! # Affine locality for relatively flat canonical module base change

Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Step 1 (local affine
reduction), and Stacks Project, Tag 08IB, first paragraph of the proof.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The affine computation makes the restriction of the canonical composite invertible
on an affine open W mapping into an affine open V of the base. This lemma identifies
restricted maps and transports cartesian squares; it does not detect global invertibility.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Step 1; Stacks Tag 08IB,
first paragraph of the proof, and Tag 08HY for the canonical mate.
(blueprint: lem-pc-canonical-module-base-change-affine-locality).

Proof: identify X' with the chosen pullback via its projection-preserving isomorphism.
The pullback-composition comparisons and their derived analogues identify the maps:
the canonical mate commutes with this identification by the adjunction unit equations.
Restrict to V in S and W in S'. Exact open restriction commutes with derived pullback,
and derived direct image commutes with restriction to a full inverse image. Under
these comparisons the restriction to W of the displayed composite is the composite
for f^{-1}(V) -> V and W -> V. The comparison c restricts to a left-derived counit
comparison: restrict its witnessing counit, use the termwise tensor restriction
identification, and commute this with the single-complex identification. Relative
flatness and quasi-coherence restrict; quasi-compactness and separatedness persist
under open base change. Identify the two affine opens with spectra of their section
rings, transport the restricted morphisms and comparison along those chart
isomorphisms, and apply haffine. Finally transport invertibility back along the
source and target comparisons. Empty W gives a zero derived category. No Cech
flatness calculation or local-to-global detection is used in this lemma. -/
theorem canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (haffine : ∀ {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (_ : Scheme.Modules.IsFlatOver G f)
    (c : (derivedPullback (pullback.fst f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))
    (_ : IsDerivedModulePullbackComparison (pullback.fst f g) G c),
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map c))
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g) [(Scheme.Modules.tensorPullback g').Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    (V : S.affineOpens) (W : S'.affineOpens) (hWV : W.1 ≤ g ⁻¹ᵁ V.1) :
    IsIso ((schemeOpenRestriction S' W.1).mapDerivedCategory.map
      (schemeDerivedBaseChangeMap f f' g g' sq.w
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage f').map c)) := by
  classical
  let U := f ⁻¹ᵁ V.1
  let fA := (f ∣_ V.1) ≫ V.2.isoSpec.hom
  let gA := W.2.isoSpec.inv ≫ g.resLE V.1 W.1 hWV ≫ V.2.isoSpec.hom
  let H := (schemeOpenRestriction X U).obj G
  have : QuasiCompact fA := by dsimp [fA]; infer_instance
  have : IsSeparated fA := by dsimp [fA]; infer_instance
  have : SheafOfModules.IsQuasicoherent.{u} H :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app G).symm
      (Scheme.Modules.isQuasicoherent_restrictFunctor U.ι G)
  have hH : Scheme.Modules.IsFlatOver H fA :=
    isFlatOver_affineOpenRestriction f G hflat V
  let (Y Z : Scheme.{u}) (a : Y ⟶ Z) : (Scheme.Modules.tensorPullback a).Additive :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction a)).left_adjoint_additive
  obtain ⟨c0, hc0, a, b, hab⟩ :=
    exists_canonicalModuleBaseChange_affineChart_comparison f g g' f' sq G c hc V W hWV
  have := haffine fA gA H hH c0 hc0
  have h := congrArg (fun k ↦ k ≫ b.inv) hab
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  rw [h]
  infer_instance

end AlgebraicGeometry
