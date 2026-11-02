import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The dual of an abelian variety has the same relative dimension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Let `A` be an abelian scheme of relative dimension `g` over an algebraically closed field
`K`, with chosen dual parameter scheme `D = dualScheme A hA`. Then the structure morphism
`D ⟶ Spec K` is smooth of relative dimension `g`. This is the dimension part of Theorem (6.18)
of Edixhoven, van der Geer and Moonen, *Abelian Varieties*, for the Library's chosen dual.
This definition states a proposition and does not prove it. -/
def AlgClosedFieldDualSchemeRelativeDimensionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ),
    A.HasRelativeDimension g → SmoothOfRelativeDimension g (dualScheme A hA).hom

end Langlands.AbelianScheme
