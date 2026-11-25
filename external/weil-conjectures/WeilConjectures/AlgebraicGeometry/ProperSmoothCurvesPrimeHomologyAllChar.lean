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
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ProperSmoothCurvesPrimeAllChar
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Prime-coefficient homology for proper smooth curve families

This is the derived-category bridge used by the finite-module dévissage.
(blueprint: lem-fd-proper-smooth-curves-prime-homology-all-char)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Total derived homology version of the all-characteristic prime-coefficient theorem.

Source: Stacks Project, more-etale.tex, Tags 0GKV and 0GKW.
(blueprint: lem-fd-proper-smooth-curves-prime-homology-all-char)

Proof: by `Etale.DerivedCategory.constructibleHomology_eq` it suffices to show, for
every integer `q`, that the `q`-th homology sheaf of the unbounded derived direct image
is constructible. `homologyRightDerivedLowerStarSingleIsoPlus` identifies it with the
`q`-th homology sheaf of the bounded below derived direct image, which is a constructible
étale module sheaf by `properSmoothCurves_prime_higherDirectImage_constructible_all_char`;
since `ULift (ZMod p)` is finite, `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`
turns this into the predicate `IsConstructibleSheaf`, which is transported along the iso.
-/
theorem properSmoothCurves_prime_higherDirectImage_constructible_homology_all_char
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (p : ℕ) [Fact p.Prime] :
    Etale.DerivedCategory.constructibleHomology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) S
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))])).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf C.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod p)))))) := by
  rw [Etale.DerivedCategory.constructibleHomology_eq]
  intro q
  let F := (constantSheaf C.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
    (ModuleCat.of _ (ULift.{u + 1} (ZMod p)))
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))) q).obj
        ((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (properSmoothCurves_prime_higherDirectImage_constructible_all_char f h_dim p q)
  exact Scheme.IsConstructibleSheaf.of_iso
    (homologyRightDerivedLowerStarSingleIsoPlus f F q).symm

end AlgebraicGeometry.Etale
