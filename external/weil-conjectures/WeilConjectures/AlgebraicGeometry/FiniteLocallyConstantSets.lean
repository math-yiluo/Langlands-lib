/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite locally constant sheaves of sets

The predicate and stable finite étale morphism property are kept below henselian comparison
proofs so that the predicate can be used in those proofs without an import cycle.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Finite étale morphisms are stable under base change. -/
instance isStableUnderBaseChange_isFinite_inf_etale :
    (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- A sheaf of sets `E` on the small étale site of `T` is *finite locally constant* if there
is an étale cover of `T` (`AlgebraicGeometry.Scheme.etalePrecoverage`) such that the
restriction of `E` to each member of the cover is constant, and the stalks of `E` at all
geometric points are finite. This is the analogue for sheaves of sets of
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`, which is stated for abelian
coefficients. -/
def Scheme.IsFiniteLocallyConstantSheafOfTypes {T : Scheme.{u}}
    (E : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T, ∀ i,
    (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧ Scheme.IsFiniteSheaf E

end AlgebraicGeometry
