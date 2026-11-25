/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.OpenPushforwardDerivedComparison

/-! # Acyclic direct images from affine opens

Source: blueprint lemma-coherent-base-change-invertible-sheaves, proof paragraphs 2 and 3.
(blueprint: lem-pc-affine-open-pushforward-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine open direct image is acyclic for a separated map to an affine scheme.
Source: blueprint lemma-coherent-base-change-invertible-sheaves, proof paragraphs 2 and 3.
(blueprint: lem-pc-affine-open-pushforward-acyclic)

Proof: X is separated over an affine base. Intersections of affine opens are affine,
so the inclusion j : W → X is affine. The composite W → Spec A is affine as both
its source and target are affine. Restriction of a quasi-coherent module to W is
quasi-coherent. Affine higher-direct-image vanishing therefore gives R^q j_* F|W = 0
and R^q (f j)_* F|W = 0 for q > 0. Restriction to W is an exact left adjoint of j_*,
so j_* preserves injectives. Apply j_* to an injective resolution of F|W.
Its augmentation is a quasi-isomorphism by j_*-acyclicity, giving an injective
resolution of j_*F|W. Computing f_* on this resolution and using pushforward
composition identifies R^p f_* (j_* F|W) with R^p (f j)_* F|W, which vanishes
for p > 0. This directly proves the comparison that the spectral sequence supplies.
This is precisely rightAcyclic for moduleDirectImage f. The empty affine open and
the zero module have zero direct images and satisfy the same conclusion. -/
theorem affine_open_pushforward_rightAcyclic
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (W : X.Opens) (hW : IsAffineOpen W) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic
      ((Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)) := by
  have := Scheme.Modules.isGrothendieckAbelian W.toScheme
  have : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ f) := inferInstance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  have hJ : (Scheme.Modules.pushforward W.ι).rightAcyclic (F.restrict W.ι) := by
    intro q
    exact Scheme.Modules.isZero_higherDirectImage_of_isAffineHom W.ι
      (F.restrict W.ι) (by omega)
  intro q
  obtain ⟨e⟩ := open_pushforward_rightDerived_comparison f W (F.restrict W.ι) hJ (q + 1)
  exact (Scheme.Modules.isZero_higherDirectImage_of_isAffineHom (W.ι ≫ f)
    (F.restrict W.ι) (q := q + 1) (by omega)).of_iso e

end AlgebraicGeometry
