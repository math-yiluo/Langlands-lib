import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Logic.Function.Basic

/-! # Finite orientation closure and its unique lattice extrema

A Boolean proposition isolating the combinatorial core of Zelevinsky (1980),
§2.8(1) and Proposition 2.10: subsets of orientations closed under correcting
one disagreeing edge toward a reference orientation.
-/

namespace Langlands.Combinatorics

universe uE

/-- For a finite edge type `E` and a reference orientation `o₀ : E → Bool`, call
a set of orientations closed if correcting any one edge on which a member
disagrees with `o₀` stays in the set. Every closed set is nonempty exactly when
it contains `o₀`, and proper exactly when it omits the opposite orientation.
The empty set, the universal set, `{o₀}`, the complement of the opposite
orientation and every edge halfspace are closed; closed sets are stable under
arbitrary intersections and unions of sets of them. The halfspaces intersect in
`{o₀}` and their union is everything except the opposite orientation. -/
def OrientationClosureExtremaStatement : Prop :=
  ∀ (E : Type uE) [Fintype E] [DecidableEq E] (o₀ : E → Bool),
    let opposite : E → Bool := fun e => !(o₀ e)
    let H : E → Set (E → Bool) := fun e => {o | o e = o₀ e}
    let Closed : Set (E → Bool) → Prop := fun S =>
      ∀ o ∈ S, ∀ e : E, o e ≠ o₀ e → Function.update o e (o₀ e) ∈ S
    (∀ S : Set (E → Bool), Closed S →
        (S.Nonempty ↔ o₀ ∈ S) ∧ (S ≠ Set.univ ↔ opposite ∉ S)) ∧
    (Closed ∅ ∧ Closed Set.univ ∧ Closed {o₀} ∧ Closed ({opposite}ᶜ) ∧
        ∀ e : E, Closed (H e)) ∧
    (∀ 𝒮 : Set (Set (E → Bool)), (∀ S ∈ 𝒮, Closed S) →
        Closed (⋂₀ 𝒮) ∧ Closed (⋃₀ 𝒮)) ∧
    ((⋂ e : E, H e) = {o₀} ∧ (⋃ e : E, H e) = Set.univ \ {opposite})

end Langlands.Combinatorics
