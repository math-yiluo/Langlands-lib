import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact

/-! # Contraction predicates for the simultaneous compact-open basis

These are the clauses of Renard V.5.2(ii)--(iv) for fixed actual subgroup
parameters. The actual reductive-group target supplies the subgroups and
character chambers; no universal existence statement is asserted here.
-/

universe u

open Set Filter Topology

namespace Langlands.BruhatTits.SpecialCompact

variable {H : Type u} [Group H]

/-- The image of a set under the actual ambient conjugation by `g`. -/
def ambientConjugate (g : H) (S : Set H) : Set H :=
  (fun x : H => g * x * g⁻¹) '' S

/-- The section `CA` normalizes the literal Levi intersection. -/
def LeviIntersectionNormalization (K M : Subgroup H) (CA : Set H) : Prop :=
  ∀ m ∈ CA,
    ambientConjugate m ((K ⊓ M : Subgroup H) : Set H) =
      ((K ⊓ M : Subgroup H) : Set H)

/-- The weak positive chamber contracts `K ∩ N`, and its inverses contract
`K ∩ Nbar`, in the ambient group. -/
def WeakChamberContraction (K N Nbar : Subgroup H) (CAplus : Set H) : Prop :=
  ∀ m ∈ CAplus,
    ambientConjugate m ((K ⊓ N : Subgroup H) : Set H) ⊆
        ((K ⊓ N : Subgroup H) : Set H) ∧
      ambientConjugate m⁻¹ ((K ⊓ Nbar : Subgroup H) : Set H) ⊆
        ((K ⊓ Nbar : Subgroup H) : Set H)

/-- Every strict-chamber element gives both exhaustive expanding unions.
The union indices are natural numbers, including zero. -/
def StrictChamberExhaustion
    (K N Nbar : Subgroup H) (CAstrict : Set H) : Prop :=
  ∀ m ∈ CAstrict,
    (N : Set H) =
        ⋃ n : ℕ, ambientConjugate ((m ^ n)⁻¹) ((K ⊓ N : Subgroup H) : Set H) ∧
      (Nbar : Set H) =
        ⋃ n : ℕ, ambientConjugate (m ^ n) ((K ⊓ Nbar : Subgroup H) : Set H)

variable [TopologicalSpace H]

/-- Uniform containment of compact subsets of either radical in expanding
conjugates. Each threshold works for every element of `CAeps ε`. -/
def UniformCompactContainment
    (K N Nbar : Subgroup H) (CAeps : ℝ → Set H) : Prop :=
  (∀ Γ : Set N, IsCompact Γ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ CAeps ε,
      N.subtype '' Γ ⊆
        ambientConjugate m⁻¹ ((K ⊓ N : Subgroup H) : Set H)) ∧
  (∀ Γ : Set Nbar, IsCompact Γ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ CAeps ε,
      Nbar.subtype '' Γ ⊆
        ambientConjugate m ((K ⊓ Nbar : Subgroup H) : Set H))

/-- The contracting powers of the literal intersection form an intrinsic
identity-neighborhood basis in `U`. The first conjunct ensures that the entire
ambient conjugate is contained in `U`. The basis sets use the intersection
`Subgroup.comap U.subtype K` in the inherited subgroup topology. -/
def ConjugatePowerNeighborhoodBasis (K U : Subgroup H) (m : H) : Prop :=
  (∀ i : ℕ,
    ambientConjugate (m ^ i) ((K ⊓ U : Subgroup H) : Set H) ⊆ (U : Set H)) ∧
  (𝓝 (1 : U)).HasBasis (fun _ : ℕ => True)
    (fun i => {x : U | ∃ y : U,
      y ∈ Subgroup.comap U.subtype K ∧
        (x : H) = m ^ i * (y : H) * (m ^ i)⁻¹})

/-- Every strictly contracting element supplies the power neighborhood basis
in `N`, and its inverse supplies the opposite-radical power basis. -/
def StrictChamberNeighborhoodBases
    (K N Nbar : Subgroup H) (CAstrict : Set H) : Prop :=
  ∀ m ∈ CAstrict,
    ConjugatePowerNeighborhoodBasis K N m ∧
      ConjugatePowerNeighborhoodBasis K Nbar m⁻¹

/-- Uniform cofinality of the contracting conjugates among all compact open
subgroups of either radical, with each subgroup's induced topology. -/
def UniformCompactOpenCofinality
    (K N Nbar : Subgroup H) (CAeps : ℝ → Set H) : Prop :=
  (∀ Γ : OpenSubgroup N, IsCompact (Γ : Set N) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ CAeps ε,
      ambientConjugate m ((K ⊓ N : Subgroup H) : Set H) ⊆
        N.subtype '' (Γ : Set N)) ∧
  (∀ Γ : OpenSubgroup Nbar, IsCompact (Γ : Set Nbar) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ CAeps ε,
      ambientConjugate m⁻¹ ((K ⊓ Nbar : Subgroup H) : Set H) ⊆
        Nbar.subtype '' (Γ : Set Nbar))

/-- The normalization, contraction, exhaustion, compact-containment and
neighborhood-cofinality clauses of Renard V.5.2(ii)--(iv) for fixed subgroup
and chamber parameters. The simultaneous actual-group target must quantify
one basis before every standard parabolic and apply this predicate to its
literal intersections and character-defined chambers. -/
def ContractionAndCofinality
    (K M N Nbar : Subgroup H)
    (CA CAplus CAstrict : Set H) (CAeps : ℝ → Set H) : Prop :=
  LeviIntersectionNormalization K M CA ∧
  WeakChamberContraction K N Nbar CAplus ∧
  StrictChamberExhaustion K N Nbar CAstrict ∧
  UniformCompactContainment K N Nbar CAeps ∧
  StrictChamberNeighborhoodBases K N Nbar CAstrict ∧
  UniformCompactOpenCofinality K N Nbar CAeps

end Langlands.BruhatTits.SpecialCompact
