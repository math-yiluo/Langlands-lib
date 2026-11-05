import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.NumberTheory.LocalField.Basic

/-! # Uniform matrix-entry bounds and canonical rational-point compactness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

/-- One nonzero scalar bounds every entry of every actual rational-point matrix. -/
def HasUniformlyBoundedEntries (ρ : MatrixRepresentation G (Fin N)) : Prop :=
  ∃ b : F, b ≠ 0 ∧ ∀ (g : rationalPoints G) (i j : Fin N),
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F) i j ≤ᵥ b

end MatrixRepresentation

/-- A closed representation with uniformly bounded entries makes the whole
canonical rational-point space compact and algebraically bounded. -/
def MatrixEntryBoundedCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      IsClosedSubgroup ρ → ρ.HasUniformlyBoundedEntries →
        letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
        IsCompact (Set.univ : Set (rationalPoints G)) ∧
          IsAlgebraicallyBounded F G.X Set.univ

end Langlands.GroupScheme
