import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Induction.BlockFactors

/-!
# Irreducibility of normalized products of supercuspidal representations

For irreducible supercuspidal representations `ρ_1, …, ρ_r` of the diagonal
blocks of a standard block shape, BZ77 Theorem 4.2 states that the normalized
product `ρ_1 × ⋯ × ρ_r` is irreducible when no `ρ_j` is isomorphic to `ν ρ_i`,
with `ν = |det|`. The converse, announced in BZ77 Remark 4.2(2), is the
singleton case of Ze80 Theorem 4.2.

The relation `ρ_j ≅ ν ρ_i` compares blocks of possibly different ranks. It is
stated as equality of rank-indexed supercuspidal isomorphism classes, so that
different ranks are never equal and no cast of a representation is needed.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

/-- BZ77 Theorem 4.2: if `ρ_j ≇ ν ρ_i` for all block indices `i, j`, the
normalized product of the irreducible supercuspidal blocks is irreducible. -/
def SupercuspidalProductIrreducibilityCriterion : Prop :=
  letI := T.topology
  ∀ (B : BlockShape n)
    (A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
    (∀ i j : Fin B.length,
      (⟨B.size j, (A j).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩) →
    ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)).IsIrreducible

/-- The converse (BZ77 Remark 4.2(2); Ze80 Theorem 4.2 for segments of length
one): if `ρ_j ≅ ν ρ_i` for some block indices `i, j`, the normalized product
of the irreducible supercuspidal blocks is not irreducible. -/
def SupercuspidalProductReducibilityTheorem : Prop :=
  letI := T.topology
  ∀ (B : BlockShape n)
    (A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
    (∃ i j : Fin B.length,
      (⟨B.size j, (A j).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
        ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩) →
    ¬ ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)).IsIrreducible

/-- Both directions over every prime, every actual finite p-adic extension,
every compatible topological realization and every positive rank. -/
def PadicSupercuspidalProductIrreducibilityTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
      SupercuspidalProductIrreducibilityCriterion.{uF, uV} F T n ∧
      SupercuspidalProductReducibilityTheorem.{uF, uV} F T n

end Langlands.Classification
