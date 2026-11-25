/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Support.SupportTriangleConstruction
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The three meanings for the specified support cone

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`def-pur-triangle-meaning` (blueprint: def-pur-triangle-meaning).

These predicates refer to the actual module functors, cone, and quotient map.
Triangle maps have all three specified components; uniqueness then expresses the
identity and composition laws. Base change specifies the map on the short exact
sequence, and all three components of the derived triangle isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Notational abbreviation for the existing category of constant-coefficient complexes.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
abbrev SupportComplex (X : Scheme.{u}) :=
  CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ

/-- A bounded below complex with injective terms; the lower bound is not fixed.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
def IsSupportInjectiveModel {X : Scheme.{u}} (I : SupportComplex Λ X) : Prop :=
  (∃ n : ℤ, I.IsStrictlyGE n) ∧ ∀ n : ℤ, Injective (I.X n)

variable {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

end AlgebraicGeometry.ProEtale
