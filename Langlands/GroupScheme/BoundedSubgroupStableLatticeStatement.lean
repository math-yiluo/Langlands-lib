import Langlands.GroupScheme.Rational.MatrixEntryBoundedness
import Mathlib.Algebra.Module.Lattice
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Stable full lattices for bounded subgroups of actual rational points

The stable-lattice step of Kaletha–Prasad Proposition 2.2.13, isolated for an
arbitrary affine group scheme over a field whose canonical valuation integer
ring is a discrete valuation ring. The existence target
`BoundedSubgroupStableLatticeStatement` is not proved here; the entry-bound
helper `MatrixRepresentation.hasBoundedRationalEntries_of_isAlgebraicallyBounded`
is proved. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {K : Type u} [Field K] [ValuativeRel K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

/-- KP regular-function bounds bound the entries of every actual representation:
each matrix entry of `ρ` is the value of the pullback under `ρ` of a general
linear entry function. The representation need not be faithful, the set need
not be a subgroup, and the valuation need not be discrete. -/
theorem hasBoundedRationalEntries_of_isAlgebraicallyBounded
    (ρ : MatrixRepresentation G n) (B : Set (rationalPoints G))
    (hB : IsAlgebraicallyBounded K G.X B) : ρ.HasBoundedRationalEntries B := by
  intro i j
  obtain ⟨b, hb, h⟩ :=
    hB (ρ.hom.hom.left.appTop (GeneralLinear.entrySection n (CommRingCat.of K) i j))
  refine ⟨b, hb, fun g hg => ?_⟩
  have hg' := h g hg
  rw [rationalPointAlgebraHom_apply_appTop] at hg'
  rw [rationalMatrix_apply_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
    ((g.left ≫ ρ.hom.hom.left).appTop
      (GeneralLinear.entrySection n (CommRingCat.of K) i j)) ≤ᵥ b
  rw [Scheme.Hom.comp_appTop]
  exact hg'

/-- `Λ` is a full lattice over the canonical valuation integer ring
(finitely generated with `K`-span everything) that is mapped into itself by
the original matrix `ρ.rationalMatrix g` of every `g ∈ B`. -/
def IsStableLatticeFor (ρ : MatrixRepresentation G n)
    (B : Subgroup (rationalPoints G))
    (Λ : Submodule (ValuativeRel.valuation K).integer (n → K)) : Prop :=
  Submodule.IsLattice K Λ ∧
    ∀ g ∈ B, ∀ v ∈ Λ, (ρ.rationalMatrix g : Matrix n n K) *ᵥ v ∈ Λ

end MatrixRepresentation

/-- The stable-lattice step of KP Proposition 2.2.13, restricted to a discrete
valuation: an algebraically bounded subgroup of the rational points of an
affine group scheme preserves some full lattice in any supplied matrix
representation. -/
def BoundedSubgroupStableLatticeStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (ValuativeRel.valuation K).integer]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
    (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
    (B : Subgroup (rationalPoints G)),
    IsAlgebraicallyBounded K G.X (B : Set (rationalPoints G)) →
      ∃ Λ : Submodule (ValuativeRel.valuation K).integer (Fin n → K),
        ρ.IsStableLatticeFor B Λ

end Langlands.GroupScheme
