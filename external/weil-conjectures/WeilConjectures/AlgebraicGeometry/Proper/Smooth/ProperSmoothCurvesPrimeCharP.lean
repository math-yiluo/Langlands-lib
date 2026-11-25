/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesArtinSchreierKernel
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearVectorBundleKernelConstructible

/-!
# Prime coefficients in proper smooth curve families in characteristic `p`

This is case (b) of Stacks Project, Tag 0GKV: the coefficient prime `p` vanishes on the base.

## References

* Stacks Project, Tag 0GKV, case (b)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- In a proper smooth family of curves with geometrically connected one-dimensional fibres
over a Noetherian base on which the prime `p` vanishes, the higher direct images of the
constant sheaf `ℤ/p` are constructible. -/
theorem properSmoothCurves_charP_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsNoetherian S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) (q : ℤ) :
    Scheme.IsConstructibleSheaf (higherDirectImage (ULift.{u + 1} (ZMod p)) f q
      ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) := by
  obtain ⟨E, _, _, F, hF, ⟨e⟩⟩ :=
    exists_forget₂_higherDirectImage_iso_frobeniusLinear_kernel f h_dim p hp q
  exact Scheme.isConstructibleSheaf_of_forget₂_iso_frobeniusLinear_kernel
    p S hp E F hF _ e

end AlgebraicGeometry.Etale
