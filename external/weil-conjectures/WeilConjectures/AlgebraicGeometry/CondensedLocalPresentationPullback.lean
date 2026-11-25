/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! Local finite presentation under normalized condensed coefficient pullback. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pullback with normalized condensed coefficients preserves local finite presentation.

Source: Bhatt--Scholze, Section 6.8; the pullback calculation in
`CondensedConstructibleSerre.lean`.
Proof: base change a pro-etale presentation cover, pull back the finite free presentation,
and transport the resulting module along the inverse coefficient comparison.
(auxiliary; not a blueprint node)
-/
theorem lfp_condensedUpperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ Y)
      ((CondensedRing.upperStar Λ f).obj M) := by
  exact localFinitePresentation_of_iso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app _).symm
    (localFinitePresentation_comap (inv (condensedPullbackHom Λ f))
      (localFinitePresentation_pullback f hM))

end AlgebraicGeometry.ProEtale
