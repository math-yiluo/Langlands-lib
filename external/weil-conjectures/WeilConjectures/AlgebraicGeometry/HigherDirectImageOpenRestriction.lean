/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives

/-! # Ordinary higher direct images commute with open restriction

Source: Stacks Project, Cohomology, Tags 01E1 and 01E5.
(blueprint: lem-pc-higher-direct-image-open-restriction).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the higher direct image to an open of the target agrees with the
higher direct image of the restricted module along the restricted morphism.
Source: Stacks Project, Cohomology, Tags 01E1 and 01E5.
(blueprint: lem-pc-higher-direct-image-open-restriction).

Proof: Apply the existing ordinary higher-direct-image restriction theorem to the
cartesian square of the two open inclusions and the restricted morphism. Its
proof restricts an injective resolution: restriction is exact and preserves
injectives, direct image commutes with this restriction termwise, and exact
restriction commutes with homology (Tags 01E1 and 01E5). The source theorem uses
pullback along the source open inclusion; Mathlib's restrictFunctorIsoPullback
identifies this pullback with the displayed restriction. Apply the degree-p
right-derived direct-image functor to this natural isomorphism and compose with
the source theorem's isomorphism. Enough injectives is supplied on both source
schemes. There are no affine, quasi-coherence or finiteness hypotheses, and the
argument includes degree zero and empty opens. -/
theorem nonempty_higherDirectImage_openRestriction_iso
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ) :
    Nonempty
      ((((RingedSpace.moduleDirectImage (f ∣_ U).toLRSHom.toShHom).rightDerived p).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) ≅
        (Scheme.Modules.restrictFunctor U.ι).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M)) := by
  let V := f ⁻¹ᵁ U
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives V.toScheme.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives V.toScheme.toRingedSpace).2
  obtain ⟨e⟩ := Scheme.Modules.nonempty_higherDirectImage_iso_restrict f M U.ι V.ι
    (f ∣_ U) (isPullback_morphismRestrict f U).flip p
  let D := (RingedSpace.moduleDirectImage (f ∣_ U).toLRSHom.toShHom).rightDerived p
  exact ⟨D.mapIso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M) ≪≫ e⟩

end AlgebraicGeometry
