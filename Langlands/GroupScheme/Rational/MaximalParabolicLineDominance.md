# The line character of a maximal standard parabolic is dominant

Author: Worker 2.

This internal helper module proves the representation-theoretic input to
Springer's overlap estimate (Springer, *Reduction theory over global fields*,
1994, Proposition 2.6 and §2.5). Springer uses a representation in which the
maximal parabolic `P_(Δ ∖ {α})` is the stabilizer of a line. He asserts that
the weight of this line is a multiple of the simple root `α`. The public errata
note `notes/errata/springer-1994-reduction-global-fields.md` records that this
is false in higher rank: the weight is a positive multiple of a fundamental
weight plus a rational character of the ambient group. This module proves the
corrected, weaker property that the proof actually needs. The weight is fixed by
the Weyl group of `Δ ∖ {α}`, and the reflection in `α` pairs it positively with
`α`. The provenance is derived. The positivity comes from the published rank-one
relation (Godement's rank-one identity, as formalized in
`RankOneStandardParabolicLineCharacter`), applied in the rank-one standard Levi
of `α`.

## Weyl elements fix characters of an intermediate subgroup

`weylAction_torusCharacterRestrict_of_factor`. Suppose a normalizing point `n`
of the torus lies in a represented subgroup `H → G` through which the torus map
factors. Then the Weyl action of `n` fixes the torus restriction of every
rational character of `H`. The proof shows that the point of `H` lifting `n`
normalizes the torus inside `H` with the same automorphism. The published
formula `weylAction_torusCharacterRestrict` then applies inside `H`, where the
character extends to `H` and is invariant under inner automorphisms.

## Matrix representation bookkeeping

In namespace `MatrixRepresentation`:

* `coordinateLineCharacter_congr`: equal representations have equal line
  characters.
* `torusCoordinateLineCharacter_restrict_comp` and
  `torusCoordinateLineCharacter_eq_restrict`: if the torus map factors as
  `T → H → G` and `H` preserves the coordinate line, then the torus line
  character equals the torus restriction of the line character of `H`.
* `HasExactCoordinateLineStabilizer.preservesCoordinateLine_restrict`: a
  homomorphism whose range lies in the exact line stabilizer preserves the line
  after restriction.

## Standard Levi invariance

`schemeWeylCharacterAction_standardLevi_restrict`: every element of the
standard relative Weyl subgroup of `K` fixes the torus restriction of every
character of the standard Levi `Standard.leviScheme i ν K`. Its normalizing
representative lies in the standard Levi (`mem_standardRelativeWeylGroup_iff`),
so the first lemma applies.

## Main theorem

`exists_maximalParabolic_dominant_line` assumes `G` connected reductive over a
field, `i` a maximal split torus, `ν` generic and `α` a simple relative root.
It produces a matrix representation `ρ` of `G` and a coordinate line `j` with
the following properties. The line is preserved by the minimal standard
parabolic `P_∅` and by the torus, with torus character `ψ`. The character `ψ` is
fixed by every element of the standard relative Weyl subgroup of `Δ ∖ {α}`.
Finally, let `f : X*(T) →+ ℤ` be a homomorphism with `f(α) = 2`, and let `w` be
an element of the standard relative Weyl subgroup of `{α}` acting by
`χ ↦ χ - f(χ) • α`. Then `f(ψ) > 0`.

Proof. Chevalley's theorem in the published form `Chevalley.exists_line_stabilizer`
gives `ρ` and `j` whose exact line stabilizer is `P_(Δ ∖ {α})`. The minimal
parabolic, the torus and the Levi of `Δ ∖ {α}` lie in `P_(Δ ∖ {α})`, by the
published parabolic order and Levi containment. So they all preserve the line,
and the invariance claim follows from the Levi invariance lemma above.

For positivity, restrict `ρ` to the rank-one standard Levi `L_α` of `{α}`. The
published `standardLevi_inter_coordinateLine_stabilizer` shows that the line
stabilizer in `L_α` is the standard parabolic of `{α} ∩ (Δ ∖ {α}) = ∅`. Then
`positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer`, applied to
`L_α` with its maximal split torus and its single simple root `α`, gives
positive natural numbers `d'` and `b` and a character `η` of `L_α` with
`d' • ψ = X + b • α`, where `X` is the torus restriction of `η`. The reflection
`w` lies in the Weyl group of `{α}`, so it fixes `X` by Levi invariance. Thus
`X - f(X) • α = X`, and applying `f` gives `f(X) - 2 f(X) = f(X)`, so
`f(X) = 0`. Applying `f` to the
relation gives `d' f(ψ) = 2b > 0`, so `f(ψ) > 0`.

The theorem does not assert that `ψ` is a multiple of `α`, or of any particular
weight. It asserts only the invariance and positivity used by
`DominantDisplacement.displacement_mem_closure`.
