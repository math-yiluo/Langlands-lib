# Twisted pseudo-coefficients when the group equals its centre

This module gives a direct low-rank argument for the target
`Langlands.BaseChange.TwistedPseudoCoefficientExistenceStatement`.
The argument handles `GL_0(E)` and `GL_1(E)` using a normalized indicator.
The test function has compact support on the group itself.

## `exists_isTwistedPseudoCoefficient_of_center_eq_top`

Let `G` be a Hausdorff, locally compact, totally disconnected topological group
with its Borel sigma-algebra and a Haar measure `μ`. Suppose every element of
`G` is central. Let `ρ` be an irreducible admissible complex representation
with central character `χ`, and let `A : ρ ≅ ρ ∘ θ` be a twisting isomorphism
for a group automorphism `θ`. Then there is a Schwartz–Bruhat function `φ` with
`IsTwistedPseudoCoefficient μ θ χ ρ hρ A φ`.
The hypotheses on `θ` here consist of its group automorphism property.

The private `centralCharacterModel` pulls `χ` back along `G → Z(G)` and uses it
to twist the trivial representation on `ℂ`. In `equivCentralCharacterModel`,
choose a nonzero vector `v` of `ρ`. The map `c ↦ c • v` from this model to `ρ`
is equivariant because all group elements act by the stated central character.
It is injective since `v ≠ 0` and surjective since its image is nonzero and `ρ`
is irreducible. This proves that `ρ` is one-dimensional. It also proves that
every other irreducible representation with central character `χ` is
isomorphic to `ρ`, by composing the two equivalences with the scalar model.
Thus there are no inequivalent representations to test for vanishing.

By smoothness choose an open subgroup fixing the image of `1` from the
scalar model, and use `Hecke.TestFunction.commonCompactOpenBiInvariance` to
choose a compact open subgroup `K` inside it. Since the image of `1`
spans the carrier, `K` fixes the entire carrier. The normalized indicator
`f` of `K` therefore has integrated action equal to the identity by
`Hecke.heckeAction_normalizedIndicator_of_fixed`. Transporting `A` to `ℂ`
conjugates it to multiplication by a nonzero complex number `a`. The
finite-rank trace of `ρ(f) ∘ A` is the ordinary trace of `A` on this
one-dimensional space, hence equals `a`. The test function `a⁻¹ • f` has
twisted trace `1`. The measure used in the normalized indicator is precisely
the supplied Haar measure.

## `generalLinear_mem_center_of_rank_le_one`

Over a commutative ring `R`, each `g : GeneralLinear n R` belongs to the centre
when `n ≤ 1`. For `n = 0` an equality of matrices has no entries to check;
for `n = 1` the unique entry of a product is the product of the unique entries,
which commute in `R`.


## Rank reduction

`TwistedPseudoCoefficientExistenceInRanks ranks` restricts the ranks of
`TwistedPseudoCoefficientExistenceStatement` to `n` with `ranks n`. The theorem
`twistedPseudoCoefficientExistenceInSmallRanks` proves it for `n ≤ 1` by
applying the central-group construction to `GL_n(E)` with the topology and Haar
measure of the existence statement.

`TwistedPseudoCoefficientRankReductionStatement` is an implication with premise
`TwistedPseudoCoefficientExistenceInRanks (fun n => 2 ≤ n)` and conclusion
`TwistedPseudoCoefficientExistenceStatement`. The theorem
`twistedPseudoCoefficientExistence_of_higherRanks` proves the implication by
splitting at `n ≤ 1` and applying the appropriate existence result. This
derived implication is the case split on rank for the Library's formulation
of Henniart–Lemaire II.5.13. All three universe parameters remain free.
