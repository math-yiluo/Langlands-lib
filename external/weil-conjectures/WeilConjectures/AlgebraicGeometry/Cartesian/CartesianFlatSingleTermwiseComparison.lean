/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianFlatSingleLocalizedBaseChange
import WeilConjectures.AlgebraicGeometry.Localized.LocalizedMixedPullbackFiniteFreeModel

/-! # Termwise comparison for a cartesian relatively flat single sheaf

Source: Stacks Project, Tags 0A1D, 06YD, 06YJ and 08FE.
(blueprint: lem-pc-cartesian-flat-single-termwise-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wT wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Cartesian single-sheaf base change followed by termwise computation on finite frees.
This has no Noetherian, coherence or approximation hypothesis or conclusion.
Source: Stacks Project, Tag 0A1D (relatively flat base change), Tags 06YD and 06YJ
(K-flat computation) and Tag 08FE (open base change).

Proof: Open base change identifies the localized restriction of Rf_*F[0] with the
 direct image of the ordinary restriction of F to the pullback along V.ι followed
 by U.ι. The cartesian square and the sheaf isomorphism identify this restricted
 sheaf with q^*M. Relative flatness of M over p makes derived tensor base change
 Tor-independent for this single sheaf: apply Tag 0A1D with the perfect unit and
 G=M[0]. It identifies this direct image with Lg^*Rp_*M[0]. Map the supplied
 representative isomorphism through Lg^*. The complex P is bounded above with
 finite free terms, hence K-flat; its restriction to W is likewise K-flat.
 Therefore derived pullback is computed by termwise tensor pullback. Composition
 of ordinary pullbacks identifies this complex with tensorPullback(g≫W.ι)(P).
 Finally transport through the exact inverse localized-site equivalence. Uniqueness
 of localization identifies Q-images even in different universes. Compute both
 right-derived images using one K-injective resolution to identify the independently
 supplied direct-image functors. The resulting isomorphisms compose as stated.
 Zero sheaves, zero-rank free terms and empty schemes are covered by the same
 computations. No bounded-below hypothesis is required: bounded above ensures K-flatness.
(blueprint: lem-pc-cartesian-flat-single-termwise-comparison). -/
theorem cartesian_flat_single_termwise_comparison
    {X S T Y : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F : X.Modules) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (V : U.toScheme.Opens) (W : T.Opens)
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (p : Y ⟶ W.toScheme) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p)
    (g : V.toScheme ⟶ W.toScheme) (q : pullback f (V.ι ≫ U.ι) ⟶ Y)
    (sq : IsPullback q (pullback.snd f (V.ι ≫ U.ι)) p g)
    (eM : Nonempty (Scheme.Modules.tensorPullbackObj q M ≅
      Scheme.Modules.tensorPullbackObj (pullback.fst f (V.ι ≫ U.ι)) F))
    (L : T.Modules ⥤ SheafOfModules.{u}
      ((moduleRings U.toScheme.toRingedSpace).over V))
    (eL : Nonempty (L ≅ Scheme.Modules.tensorPullback (g ≫ W.ι) ⋙
      (Scheme.Modules.overEquiv V).inverse)) [L.Additive]
    (P : CochainComplex T.Modules ℤ)
    (hP : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := moduleRings T.toRingedSpace) (ULift.{u} (Fin r))))
    (eP : Nonempty ((schemeOpenRestriction T W).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ (schemeDerivedDirectImage p).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M))) :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
      ((schemeOpenRestriction S U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  by
    classical
    obtain ⟨b⟩ := cartesian_flat_single_localized_baseChange f F U V W p M hM g q sq eM
    obtain ⟨c⟩ := localizedMixedDerivedPullback_finiteFree_model U V W g L eL P hP hfree
    let H := localizedMixedDerivedPullback U V W g
    exact ⟨b ≪≫ H.mapIso (Classical.choice eP).symm ≪≫ c⟩

end AlgebraicGeometry
