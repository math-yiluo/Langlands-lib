import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.PairLieAlgebra

/-! # Torus-weight grading of the tangent Lie algebra of a pair of representations

This module states the group-side facts about the pair Lie algebra
`MatrixRepresentation.pairLieAlgebra σ ρ` that the Casimir proof of Freudenthal's
multiplicity formula uses. The grading is by the weights of the split maximal torus on
the product of the two coordinate spaces: an endomorphism has degree `χ` when it carries
every weight-`μ` vector to a weight-`(μ + χ)` vector. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)
  {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The weight-`μ` space of the product of the coordinate spaces of `σ` and `ρ`. -/
def pairWeightSpace (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (μ : characterLattice p.torus) : Submodule k ((m → k) × (n → k)) :=
  (p.representationWeightSpace σ μ).prod (p.representationWeightSpace ρ μ)

/-- The endomorphisms of the product that raise every torus weight by `χ`. -/
def weightShift (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (χ : characterLattice p.torus) : Submodule k (Module.End k ((m → k) × (n → k))) where
  carrier := {f | ∀ μ, ∀ u ∈ p.pairWeightSpace σ ρ μ, f u ∈ p.pairWeightSpace σ ρ (μ + χ)}
  add_mem' := by
    intro f g hf hg μ u hu
    exact Submodule.add_mem _ (hf μ u hu) (hg μ u hu)
  zero_mem' := by
    intro μ u _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c f hf μ u hu
    exact Submodule.smul_mem _ c (hf μ u hu)

theorem mem_weightShift (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (χ : characterLattice p.torus) (f : Module.End k ((m → k) × (n → k))) :
    f ∈ p.weightShift σ ρ χ ↔
      ∀ μ, ∀ u ∈ p.pairWeightSpace σ ρ μ, f u ∈ p.pairWeightSpace σ ρ (μ + χ) :=
  Iff.rfl

/-- An endomorphism of the product acts as the cocharacter `y` would differentiate: by the
integer `⟨μ, y⟩` on every weight-`μ` vector. -/
def IsCocharacterAction (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (y : cocharacterLattice p.torus) (x : Module.End k ((m → k) × (n → k))) : Prop :=
  ∀ μ, ∀ u ∈ p.pairWeightSpace σ ρ μ, x u = ((p.rootDatum.toLinearMap μ y : ℤ) : k) • u

variable [LocallyOfFiniteType G.X.hom]

/-- The degree-`χ` part of the pair Lie algebra. -/
def pairLieGraded (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (χ : characterLattice p.torus) : Submodule k (Module.End k ((m → k) × (n → k))) :=
  (MatrixRepresentation.pairLieAlgebra σ ρ).toSubmodule ⊓ p.weightShift σ ρ χ

/-- The group-side facts about the pair Lie algebra used by the Casimir proof of
Freudenthal's formula:
* the pair Lie algebra is spanned by its homogeneous parts;
* every cocharacter `y` gives an element acting by `⟨μ, y⟩` on weight `μ`;
* the degree-zero part is spanned by such cocharacter elements;
* a nonzero degree that is not a root has zero part, and every root part is a line;
* every nonzero cocharacter pairs nontrivially with some weight of `σ`. -/
def PairLieWeightData (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n) :
    Prop :=
  (MatrixRepresentation.pairLieAlgebra σ ρ).toSubmodule ≤
      (⨆ χ : characterLattice p.torus, p.pairLieGraded σ ρ χ) ∧
    (∀ y : cocharacterLattice p.torus,
      ∃ x ∈ MatrixRepresentation.pairLieAlgebra σ ρ, p.IsCocharacterAction σ ρ y x) ∧
    p.pairLieGraded σ ρ 0 ≤
      Submodule.span k {x | ∃ y : cocharacterLattice p.torus, p.IsCocharacterAction σ ρ y x} ∧
    (∀ χ : characterLattice p.torus, χ ≠ 0 → χ ∉ Set.range p.rootDatum.root →
      p.pairLieGraded σ ρ χ = ⊥) ∧
    (∀ i : p.rootIndex, Module.finrank k (p.pairLieGraded σ ρ (p.rootDatum.root i)) = 1) ∧
    ∀ y : cocharacterLattice p.torus, y ≠ 0 →
      ∃ μ : characterLattice p.torus,
        p.representationWeightSpace σ μ ≠ ⊥ ∧ p.rootDatum.toLinearMap μ y ≠ 0

end SplitPinning

/-- For a split pinning of a locally finite type group scheme over a field of
characteristic zero, every closed linear embedding `σ` and every finite representation `ρ`
satisfy `PairLieWeightData`. -/
def PairLieWeightDataStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (p : SplitPinning G) (N n : ℕ) (σ : MatrixRepresentation G (Fin N))
    (ρ : MatrixRepresentation G (Fin n)),
    IsClosedSubgroup σ → p.PairLieWeightData σ ρ

end Langlands.GroupScheme
