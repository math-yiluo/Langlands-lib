import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Projection on a cone in a Euclidean space (Renard V.5.5)

In a finite-dimensional real inner product space, every vector has a unique nearest point in
the closure of a nonempty convex open cone `C`, characterized by an obtuse-angle inequality and,
when `C` is not the whole space, by membership of `v₀ - v` in the closure of the dual cone `Č`
together with `⟨v - v₀, v₀⟩ = 0` (Proposition). For the open cone spanned by the dual basis
`ω` of a basis `α`, every vector is uniquely `∑_{i ∉ F} tᵢ ωᵢ - ∑_{j ∈ F} sⱼ αⱼ` with `tᵢ > 0`,
`sⱼ ≥ 0`, and `∑_{i ∉ F} tᵢ ωᵢ` is then its projection on the closed cone (Corollary).
-/

namespace Langlands.Renard

universe u v

open scoped BigOperators

/-- Renard V.5.5, Proposition: let `E` be a finite-dimensional real inner product space and
`C` a nonempty convex open cone of `E`, with dual cone `Č = {v | ∀ w ∈ C, 0 < ⟨v, w⟩}`. For every
`v` there is a unique `v₀` in the closure of `C` such that (i) `‖v - v₀‖ ≤ ‖v - w‖` for every `w`
in the closure of `C`. Moreover, for `v₀` in the closure of `C`, (i) is equivalent to
(ii) `⟨v - v₀, w - v₀⟩ ≤ 0` for every `w` in the closure of `C`, and, when `C ≠ E`, to
(iii) `v₀ - v` lies in the closure of `Č` and `⟨v - v₀, v₀⟩ = 0`. -/
def ConeProjectionStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E), IsOpen C → Convex ℝ C → C.Nonempty →
    (∀ t : ℝ, 0 < t → ∀ x ∈ C, t • x ∈ C) →
    let Cdual : Set E := {u | ∀ w ∈ C, 0 < inner ℝ u w}
    ∀ v : E,
      (∃! v₀ : E, v₀ ∈ closure C ∧ ∀ w ∈ closure C, ‖v - v₀‖ ≤ ‖v - w‖) ∧
      ∀ v₀ ∈ closure C,
        ((∀ w ∈ closure C, ‖v - v₀‖ ≤ ‖v - w‖) ↔
          ∀ w ∈ closure C, inner ℝ (v - v₀) (w - v₀) ≤ 0) ∧
        (C ≠ Set.univ →
          ((∀ w ∈ closure C, ‖v - v₀‖ ≤ ‖v - w‖) ↔
            v₀ - v ∈ closure Cdual ∧ inner ℝ (v - v₀) v₀ = 0))

/-- Renard V.5.5, Corollary: let `α` be a basis of the finite-dimensional real inner product
space `E`, indexed by a finite type, and `ω` its dual basis (`⟨αᵢ, ωⱼ⟩ = δᵢⱼ`); let `C` be the open
cone `{∑ tᵢ ωᵢ | tᵢ > 0}`. For every `v` there is a unique finite set `F` of indices such that
`v = ∑_{i ∉ F} tᵢ ωᵢ - ∑_{j ∈ F} sⱼ αⱼ` with `tᵢ > 0` and `sⱼ ≥ 0`; and for any such decomposition
`∑_{i ∉ F} tᵢ ωᵢ` is the projection of `v` on the closure of `C`: it lies in the closure of `C`
and is nearest to `v` there. -/
def ConeProjectionBasisStatement : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (α : Module.Basis ι ℝ E) (ω : ι → E),
    (∀ i j : ι, inner ℝ (α i) (ω j) = if i = j then 1 else 0) →
    let C : Set E := {x | ∃ t : ι → ℝ, (∀ i, 0 < t i) ∧ x = ∑ i, t i • ω i}
    ∀ v : E,
      (∃! F : Finset ι, ∃ t s : ι → ℝ,
        (∀ i ∈ Finset.univ \ F, 0 < t i) ∧ (∀ j ∈ F, 0 ≤ s j) ∧
          v = (∑ i ∈ Finset.univ \ F, t i • ω i) - ∑ j ∈ F, s j • α j) ∧
      ∀ (F : Finset ι) (t s : ι → ℝ),
        (∀ i ∈ Finset.univ \ F, 0 < t i) → (∀ j ∈ F, 0 ≤ s j) →
        v = (∑ i ∈ Finset.univ \ F, t i • ω i) - ∑ j ∈ F, s j • α j →
          (∑ i ∈ Finset.univ \ F, t i • ω i) ∈ closure C ∧
            ∀ w ∈ closure C, ‖v - ∑ i ∈ Finset.univ \ F, t i • ω i‖ ≤ ‖v - w‖

/-- Renard V.5.5: the Proposition and the Corollary. -/
def ConeProjectionStatements.{u', v'} : Prop :=
  ConeProjectionStatement.{v'} ∧ ConeProjectionBasisStatement.{u', v'}

end Langlands.Renard
