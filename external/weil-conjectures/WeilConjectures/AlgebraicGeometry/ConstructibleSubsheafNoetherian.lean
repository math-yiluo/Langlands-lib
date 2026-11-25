/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian

/-!
# Subsheaves of constructible module sheaves on Noetherian schemes

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, and Stacks Project,
Proposition 59.74.1(3), Tag 03RY
(blueprint: lem-weil-pbc-constructible-subobjects-noetherian).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every subsheaf of a constructible sheaf of modules over a finite commutative ring
on the small etale site of a Noetherian scheme is constructible.
Source: Stacks Project, Proposition 59.74.1(3), Tag 03RY
(blueprint: lem-weil-pbc-constructible-subobjects-noetherian).

Proof:
Compare finite constant-value constructibility with `IsConstructibleSheaf` using
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`. A finite commutative ring is Noetherian.
Apply `constructible_of_mono_noetherian`, whose proof uses generic constancy of
module subobjects followed by Noetherian induction on closed subsets, and convert
back with the same comparison. -/
theorem isConstructibleEtaleModuleSheaf_of_mono_noetherian
    {T : Scheme.{u}} [IsNoetherian T] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {G F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf G := by
  have : IsConstructibleSheaf F :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr
    (constructible_of_mono_noetherian i)

end AlgebraicGeometry.Scheme
