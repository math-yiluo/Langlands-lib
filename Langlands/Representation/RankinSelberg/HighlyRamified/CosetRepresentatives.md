# Finite sets of coset representatives

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. It supplies the
finite set `T₂` of translates used to build the test vector of Jacquet–Shalika 1985, §4.4,
from the weight (4.4.18): the source integrates against a locally constant compactly supported
function, and the Library test vector is the corresponding finite sum.

- `exists_finset_addCosetReps K L hK hL`: for a compact additive subgroup `K` and an open
  additive subgroup `L` of a topological additive group, there is a finite set `T ⊆ K` whose
  elements are pairwise incongruent modulo `L` and such that every element of `K` is congruent
  modulo `L` to an element of `T`. The proof takes `Quotient.out` of every class of the finite
  quotient `K ⧸ (L ∩ K)`. The quotient is finite by Mathlib's
  `AddSubgroup.quotient_finite_of_isOpen`; this is the argument of the published
  `exists_finset_leftCosets` in `GodementJacquet/WhittakerCosetSum`.
- `sum_reps_eq L Φ hΦ T hT hcov y`: if `Φ` is `L`-periodic, the elements of `T` are pairwise
  incongruent modulo `L`, and every point of the support of `Φ` is congruent to an element of
  `T`, then `Σ_(t ∈ T, t - y ∈ L) Φ(t) = Φ(y)`. The codomain of `Φ` is any additive commutative
  monoid.
