import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation

/-! # Actual highest-weight representations at the fundamental weights -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The additive monoid of nonnegative integral combinations of simple roots. -/
def positiveRootMonoid : AddSubmonoid (characterLattice p.torus) :=
  AddSubmonoid.closure (Set.range fun a : p.base.support => p.rootDatum.root a)

theorem simpleRoot_mem_positiveRootMonoid (a : p.base.support) :
    p.rootDatum.root a ∈ p.positiveRootMonoid :=
  AddSubmonoid.subset_closure ⟨a, rfl⟩

/-- The actual all-algebra character space of a representation restricted to the
supplied split maximal torus. -/
def representationWeightSpace {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (lam : characterLattice p.torus) :
    Submodule k (n → k) :=
  letI := p.isSplitTorus.isAffineHom
  (ρ.restrict p.inclusion).characterSpace
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)

/-- An irreducible actual representation with a one-dimensional highest-weight
space, a complete torus-weight decomposition, and weights below `lam`. -/
def IsHighestWeight {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (lam : characterLattice p.torus) : Prop :=
  ρ.IsIrreducible ∧
    (⨆ μ : characterLattice p.torus, p.representationWeightSpace ρ μ) = ⊤ ∧
    Module.finrank k (p.representationWeightSpace ρ lam) = 1 ∧
    ∀ μ : characterLattice p.torus, p.representationWeightSpace ρ μ ≠ ⊥ →
      lam - μ ∈ p.positiveRootMonoid

/-- The integral duality equations defining the fundamental weight at `a`. -/
def IsFundamentalWeight (a : p.base.support) (lam : characterLattice p.torus) : Prop := by
  classical
  exact ∀ b : p.base.support,
    p.rootDatum.toLinearMap lam (p.rootDatum.coroot b) = if b = a then 1 else 0

/-- An actual finite matrix representation at a fundamental highest weight.
This data type asserts no existence. -/
structure FundamentalRepresentation (a : p.base.support) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  highestWeight : characterLattice p.torus
  isFundamentalWeight : p.IsFundamentalWeight a highestWeight
  isHighestWeight : p.IsHighestWeight representation highestWeight

namespace FundamentalRepresentation

variable {p} {a : p.base.support} (F : p.FundamentalRepresentation a)

/-- When simple coroots form an integral basis, the supplied highest weight is
exactly the previously published fundamental weight. -/
theorem highestWeight_eq_fundamentalWeightBasis
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) :
    F.highestWeight =
      Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a := by
  classical
  apply p.rootDatum.toLinearMap.toPerfPair.injective
  apply (Langlands.RootDatum.simpleCorootBasis p.rootDatum p.base hspan).ext
  intro b
  change p.rootDatum.toLinearMap F.highestWeight
      (Langlands.RootDatum.simpleCorootBasis p.rootDatum p.base hspan b) =
    p.rootDatum.toLinearMap
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a)
      (Langlands.RootDatum.simpleCorootBasis p.rootDatum p.base hspan b)
  rw [Langlands.RootDatum.simpleCorootBasis_apply,
    Langlands.RootDatum.fundamentalWeightBasis_pairing]
  exact F.isFundamentalWeight b

end FundamentalRepresentation
end SplitPinning

/-- Over an algebraically closed field, every actual simply connected group
with supplied split pinning has a fundamental highest-weight representation
for each simple root. -/
def SplitFundamentalRepresentationsExistStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ a : p.base.support, Nonempty (p.FundamentalRepresentation a)

end Langlands.GroupScheme
