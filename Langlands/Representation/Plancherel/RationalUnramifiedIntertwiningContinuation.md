# Equivariance of continued rational operator families

This derived construction supplies the equivariance part of the continuation
step motivated by Waldspurger, *La formule de Plancherel pour les groupes
p-adiques*, IV.1, printed pp.276–277 / PDF pp.42–43. The source starts with
intertwiners of normalized inductions and continues their rational families in
fixed compact pictures. This file proves an algebraic equivariance principle for
the constructed linear continuation under explicitly polynomial varying actions.
The specialization to actual normalized induction remains separate.

## Parameters and hypotheses

The character parameters are
`unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)` for a
connected reductive group scheme `G` over a nonarchimedean local field `F`.
The local-field universe and characteristic are arbitrary. The rational-point
topology is supplied, and continuity of `rationalValuationImageProjection G`
is explicit. Neither splitness nor quasisplitness is assumed.

The original parameter region `Ω` contains a nonempty subset `D` open in the
full character topology. Openness of `Ω` itself is unnecessary. Source and target
are complex vector spaces `V` and `W` in independent universes, without carrier
topologies or dimension assumptions.

`RationalOperatorContinuationData Ω A` is the existing record of one regular
denominator, nonvanishing on `Ω`, and a globally polynomial linear numerator
whose restriction is that denominator times `A`. Its `regularRegion` is the
denominator's nonzero locus, and its `continuedOperator` divides the numerator
there. The imported `rationalOperatorContinuation` constructs such data from
`IsRationalOperatorOn Ω A` under the displayed open-set hypotheses; no new
continuation data are postulated by this file.

For the equivariant construction, `H` is any monoid in an independent universe.
The families `ρ` and `σ` assign representations of `H` on `V` and `W` to every
character. For each fixed `g : H`, their action operators must be polynomial
families in the existing finite-vector sense on the entire character space.
These are explicit mathematical hypotheses. The parameter group scheme `G`
and the acting monoid `H` need not have the same underlying points.

## Global numerator equation

`rationalOperatorContinuation_numerator_commutes` takes polynomial endomorphism
families `R` and `S` and an equation
`A(χ) ∘ R(χ) = S(χ) ∘ A(χ)` throughout `Ω`. It proves the same equation with
the global numerator in place of `A` at every character, including zeros of
the selected denominator.

For each fixed input vector, both composed numerator expressions are polynomial
by the imported varying-operator composition law. On `D` the clearing equation
and linearity reduce their difference to zero. The actual-character polynomial
vector uniqueness theorem makes that difference zero everywhere. This uses no
inverse of a denominator and hence applies even at its zeros.

`rationalOperatorContinuation_commutes` then proves the equation for the
continued operators throughout `regularRegion`. Its proof takes the global
numerator equation, multiplies by the inverse denominator and uses linearity of
`S`. No continued value at a zero is defined.

## Bundled intertwiners

Let `J(χ)` be a supplied intertwiner from `ρ(χ)` to `σ(χ)` on `Ω`, and let `p`
be continuation data for its underlying linear maps. `continuedIntertwiner`
has underlying linear map `p.continuedOperator` and is an actual
`Representation.IntertwiningMap` at each point of `p.regularRegion`.
Its equivariance field applies the preceding theorem to `ρ(χ)(g)` and
`σ(χ)(g)` for every `g`.

`continuedIntertwiner_toLinearMap` identifies its underlying map definitionally.
`continuedIntertwiner_rational` reuses rationality of the divided numerator.
`continuedIntertwiner_agrees` recovers `J` at every original parameter using
the imported underlying-map recovery theorem and extensionality of
intertwiners. `continuedIntertwiner_unique` applies the underlying continuation
uniqueness theorem to two records for the same original `J`. The resulting
intertwiners agree at every point of the intersection of their regular regions,
even if the denominators differ.

## Source correspondence and remaining obligations

The source at printed p.276 introduces `G`-invariant operators between actual
normalized inductions. Printed p.277 identifies them in fixed compact pictures,
uses finite regular expansions with one whole-operator denominator, and extends
to that denominator's nonzero locus. This file implements the algebraic
propagation of equivariance for varying polynomial actions; its proof uses
actual-character uniqueness rather than constructing the source's
`G`–`B`-module specialization model.

It does not yet construct the varying compact-picture induction action or prove
its polynomiality. Neither the actual standard-integral convergence and
rationality nor descent from character parameters to representation classes is
proved here. A maximal regular region, generic induced irreducibility, the
global scalar `j`, `mu` and any main Plancherel assertion remain outside this
unit. The rationality and action-polynomiality premises cannot be counted as
permitted external structural hypotheses discharging the standing program.
