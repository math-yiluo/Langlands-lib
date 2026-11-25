/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.AlgebraicGeometry.EtaleBaseChangeRestrictScalars
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients

/-!
# Reflection of higher-direct-image vanishing under restriction of coefficients

Source: Stacks Project, Tag 03FD and Tag 0D6J.
(blueprint: lem-sbc-coefficient-higher-direct-image-zero)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Restriction of scalars detects vanishing of a higher direct image.

Source: Stacks Project, Tags 03FD and 0D6J.
(blueprint: lem-sbc-coefficient-higher-direct-image-zero)

Proof: apply the existing base-change coefficient comparison to the identity Cartesian
square with right vertical map h. The base-change target identifies with higher direct
image because pullback along the identity is the identity. Restriction of scalars
preserves zero morphisms and is faithful; it therefore preserves and reflects zero
objects, by the criterion that the identity morphism is zero. -/
theorem isZero_higherDirectImage_restrictScalars_iff
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    IsZero (higherDirectImage R h q ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj F)) ↔
      IsZero (higherDirectImage S h q F) := by
  let HR := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0 ⋙
    R+((h)_*[ModuleCat.{u + 1} R]) ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  let HS := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) 0 ⋙
    R+((h)_*[ModuleCat.{u + 1} S]) ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  let FR := (Sheaf.restrictScalars Y.smallEtaleTopology φ).obj F
  let UR := Sheaf.restrictScalars X.smallEtaleTopology φ
  obtain ⟨_, b, _⟩ := restrictScalars_baseChange_comparison φ (IsPullback.id_horiz h) q F
  let iR : (baseChangeTargetFunctor R (𝟙 Y) h q).obj FR ≅ HR.obj FR :=
    (baseChangeTargetFunctorIso R (𝟙 Y) h q).app FR ≪≫
      HR.mapIso ((upperStarId (ModuleCat.{u + 1} R) Y).app FR)
  let iS : (baseChangeTargetFunctor S (𝟙 Y) h q).obj F ≅ HS.obj F :=
    (baseChangeTargetFunctorIso S (𝟙 Y) h q).app F ≪≫
      HS.mapIso ((upperStarId (ModuleCat.{u + 1} S) Y).app F)
  let i : HR.obj FR ≅ UR.obj (HS.obj F) := iR.symm ≪≫ b ≪≫ UR.mapIso iS
  change IsZero (HR.obj FR) ↔ IsZero (HS.obj F)
  rw [i.isZero_iff]
  constructor
  · intro hz
    rw [IsZero.iff_id_eq_zero] at hz ⊢
    exact UR.map_injective (by simpa using hz)
  · exact UR.map_isZero

end AlgebraicGeometry.Etale
