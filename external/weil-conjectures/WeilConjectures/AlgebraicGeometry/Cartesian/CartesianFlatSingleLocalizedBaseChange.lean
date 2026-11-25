/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.LocalizedMixedDerivedPullback

import WeilConjectures.AlgebraicGeometry.Picard.NestedOpenSingleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Localized.LocalizedCartesianFlatSingleComparison

/-! # Localized cartesian base change for a relatively flat single sheaf
Source: Stacks Project, Tags 0A1D and 08FE.
(blueprint: lem-pc-cartesian-flat-single-localized-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wT wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Cartesian base change for the single sheaf, before choosing any representative.
Source: Stacks Project, Tags 0A1D and 08FE.
Proof: combine restriction to U and to V into restriction along V.ι followed by U.ι.
Open base change identifies this restriction of Rf_*F[0] with direct image from the
cartesian pullback source. The supplied sheaf isomorphism identifies its coefficient
sheaf with q^*M. Apply relatively flat tensor base change to p with perfect factor
O_Y[0] and relatively flat single factor M[0]. The tensor unit identifications remove
the perfect factor. The given cartesian square identifies the canonical pullback
source with the supplied one; conjugating direct image by this scheme isomorphism
identifies the output with Lg^*Rp_*M[0]. Compute direct images with one K-injective
resolution to compare the supplied localization models with standard ones. Canonical
localization equivalences intertwine Qh, hence also Q and the single functors.
Finally apply the inverse exact localized-site equivalence for V. This gives exactly
the transported pullback in localizedMixedDerivedPullback. No complex P, Noetherian
approximation, coherence of the direct image, or finite presentation is used. Zero
sheaves and empty schemes satisfy all of these functorial comparisons unchanged.
(blueprint: lem-pc-cartesian-flat-single-localized-base-change). -/
theorem cartesian_flat_single_localized_baseChange
    {X S T Y : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
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
 :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
      ((schemeOpenRestriction S U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) ≅
      (localizedMixedDerivedPullback U V W g).obj
        ((schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M))) := by
  classical
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let := dV
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace))
  let E := (Scheme.Modules.overEquiv V).inverse
  let : E.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨a⟩ := nestedOpen_single_directImage_comparison f F U V
  obtain ⟨b⟩ := localized_cartesian_flat_single_comparison U V W p M hM g q
    (pullback.snd f (V.ι ≫ U.ι)) sq
  let c := (@Functor.mapDerivedCategory _ _ _ dV _ _ _ _ E _ _ _).mapIso
    ((schemeDerivedDirectImage (pullback.snd f (V.ι ≫ U.ι))).mapIso
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace)) 0).mapIso
          (Classical.choice eM)))
  exact ⟨a ≪≫ c.symm ≪≫ b⟩

end AlgebraicGeometry
