# The Tits obstruction on star-fixed weights

This module constructs the Tits obstruction
`α : (star-fixed weights) →+ BrauerGroup k`. It follows the first assertion
of Corollary 3.5 of Tits, *Représentations linéaires irréductibles d'un groupe
réductif sur un corps quelconque*, J. reine angew. Math. 247 (1971), p. 205.
The map on dominant
star-fixed weights, which sends `λ` to the class of the Tits algebra of the
irreducible representation of highest weight `λ` (published predicate
`IsHighestWeight`, which includes irreducibility), is a monoid homomorphism. It extends to
the group of star-fixed weights.

The target is Mathlib's matrix-stable quotient `BrauerGroup.{u,u} k`, with
the additive group law built in `Langlands/Algebra/BrauerGroup`
(`classOf`, `classOf_tensor`, `classOf_eq_iff`). The
construction works over any field `k`,
in any characteristic, for any Galois extension `K/k` with a Galois pinning
`d`. There is no inner-type hypothesis.

The construction takes one hypothesis, `hspan : corootSpan ℤ = ⊤`, which
holds for simply connected groups by the published
`corootSpan_eq_top_of_simplyConnected`. The highest-weight input is the
published `splitHighestWeightClassification`, used through
`Reductive/TitsDominantClass`.

## Declarations

- `dominantTitsClass_congr`: the dominant Tits class (`dominantTitsClass` of
  `Reductive/TitsDominantClass`) depends only on the weight, not on the
  proofs of dominance and star-fixedness.
- `dominantTitsClass_add`: for dominant star-fixed `a` and `b`, the class of
  `a + b` is the sum of the classes of `a` and `b`. Choose representations of
  highest weights `a`, `b` and `a + b` with `splitHighestWeightClassification`.
  Then apply
  `dominantTitsClass_eq`, the additivity theorem
  `titsCSAOf_add_isBrauerEquivalent` of `Reductive/TitsAdditivity`, and
  `classOf_tensor`.
- `isDominantWeight_zero` and `isStarFixedWeight_zero`. `dominantTitsClass_zero`:
  the class of `0` vanishes. It equals twice itself by additivity.
- `titsObstructionValue hspan λ hfix` is defined as
  `[dominantPart λ] - [dominantPart λ - λ]`. Both weights are dominant and
  star-fixed by `Reductive/StarFixedDominantDecomposition`.
- `titsObstructionValue_eq_sub`: the value does not depend on the
  decomposition. If `λ = a - b` with `a`, `b` dominant and star-fixed, then
  the value is `[a] - [b]`. Writing `p = dominantPart λ`, we have
  `p + b = a + (p - λ)`, so additivity gives `[p] + [b] = [a] + [p - λ]`.
- `titsObstructionValue_of_isDominantWeight`: on a dominant star-fixed `λ`
  the value is the dominant Tits class of `λ`. Use the decomposition
  `λ = λ - 0`.
- `titsObstructionValue_eq_classOf`: on a dominant star-fixed `λ`, the value
  is `classOf (titsCSAOf ρ)` for every `ρ` with `IsHighestWeight ρ λ` (an
  irreducible representation of highest weight `λ`). This is the
  identification with the actual Tits algebra of the irreducible
  highest-weight representation, independent of the choice of such `ρ`.
- `titsObstructionValue_add`: the value is additive. Decompose `λ + μ` as
  `(dominantPart λ + dominantPart μ) -
  ((dominantPart λ - λ) + (dominantPart μ - μ))` and use
  `titsObstructionValue_eq_sub` together with `dominantTitsClass_add`.
- `titsObstructionOn S hS`: for any additive subgroup `S` of the character
  lattice consisting of star-fixed weights, `titsObstructionValue` is an
  additive map `S →+ BrauerGroup.{u,u} k`. The zero is preserved by
  `dominantTitsClass_zero`; addition by `titsObstructionValue_add`.
