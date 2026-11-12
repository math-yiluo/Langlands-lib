# Counting points from a finite relative normalization cover

Author: Worker 90.

This internal counting development uses the uniform finite-morphism bound and
the coordinate count for relative affine space.

`affineNormalizationPointEquiv` decomposes the actual `K`-points of a scheme
mapping to relative affine space above a fixed point of the base into pairs:
an affine-space point above that base point, and a point of the source above
that affine-space point. Both directions are composition or forgetting this
image, and the inverse laws use the defining equations.

`exists_uniform_card_affineNormalization_le` applies the uniform finite-morphism
bound to a finite map to relative affine `d`-space over an affine base.
For each finite-field point of the base, the displayed equivalence gives
finiteness and a sum of the fibre counts over the `q^d` affine-space points.
Every summand is at most the same natural number `N`, selected before the
finite field or base point. The result is a bound `N q^d`.

## A supplied cover

`FiniteNormalizationCover.exists_uniform_nat_card_fibrePoints_le` takes actual
geometric cover data for a morphism `f : X → S`. It produces a positive natural
number `N` such that every finite-field base point `s` and every natural `e`
with `dim(X_y) ≤ e`, for `y = s(closedPoint K)`, have a finite type of actual
lifts `Spec K → X` and at most `N q^e` such lifts.

For each piece, the proof chooses the natural bound from
`exists_uniform_card_affineNormalization_le`. For a fixed base point, if the
piece has no lifts there is nothing to count. Otherwise one lift determines a
map `t : Spec K → Tᵢ`. Every lift in the piece induces this same `t`, because
the immersion `Tᵢ → S` is a categorical monomorphism. Thus the piece's lift
type injects into the type already bounded by `Nᵢ q^(dᵢ)`.

The image of the closed point under `t` maps to `y`. The cover's dimension
comparison and the given upper bound for `dim(X_y)` imply `dᵢ ≤ e`. A finite
field has at least one element, so `q^(dᵢ) ≤ q^e`. The covering condition
gives a surjection from the finite disjoint union of these piece lift types
to the type of lifts to `X`. Summing the bounds gives
`(∑ Nᵢ) q^e`; the proof chooses `N = (∑ Nᵢ) + 1` to ensure positivity.
Overlaps of pieces only enlarge this upper bound. Finiteness is proved
explicitly, so no inequality relies on `Nat.card` being zero for an infinite
type.

## Conditional reduction of the family statement

`familyPointUpperBound_of_finiteNormalizationCover` proves the implication
`FiniteNormalizationCoverStatement → FamilyPointUpperBoundStatement`.
For a base of finite type over `Spec (ULift ℤ)`, the proof derives
Noetherianity from the Noetherian ring `ℤ` and compactness of the base. The
hypothesis then supplies a cover. Its positive natural bound, cast to the
real numbers, gives precisely the published family statement, with its
original fibre dimension and its original type of actual lifts.

Provenance: internal elementary cardinality assembly and a formal reduction.
The equivalence and finite-normalization estimate use no
normalization-existence hypothesis. The cover bound requires a supplied
cover, and the final implication has the geometric existence statement as
its explicit antecedent. This module does not prove that antecedent or the
unconditional `FamilyPointUpperBoundStatement`. It uses no external
point-count estimate.
