# Relative degree-two cocycle normal form and inflation injectivity

Authors: Worker 145, with the mathematical interface supplied by Worker 138.

This module defines two proposition targets. It proves neither proposition.
Both quantify a commutative ring `k : Type u`, a group `G : Type u`,
a representation `A : Rep.{u} k G`, and a normal subgroup `S : Subgroup G`,
for an arbitrary common universe `u`. Both assume
`Subsingleton (groupCohomology (Rep.res S.subtype A) 1)`.
Since this cohomology module has a zero element, the assumption says that
every class in `H¹(S, A)` is zero. These are the same parameters and the
same vanishing hypothesis as the published
`Langlands.Cohomology.H2InflationRestrictionExactness`.
There are no finiteness, topology, field, or trivial-action assumptions.

## Relative cocycle normal form

`Langlands.Cohomology.H2RelativeCocycleNormalForm` states that, for every
`c : groupCohomology.cocycles₂ A` whose restriction to `S × S` is a
coboundary, there is a one-cochain `b : G → A` such that
`c - groupCohomology.d₁₂ A b` vanishes whenever either argument lies in `S`.

Here `cocycles₂ A` is Mathlib's submodule of functions `G × G → A`
annihilated by the inhomogeneous differential `d₂₃`. Thus its elements
satisfy, for all `g, h, j : G`,

`A.ρ g (c (h, j)) - c (g * h, j) + c (g, h * j) - c (g, h) = 0`.

The cochains are not assumed to be normalized at the identity. The actual
Mathlib differential `groupCohomology.d₁₂ A` is used, with convention

`(d₁₂ A b) (g, h) = A.ρ g (b h) - b (g * h) + b g`.

The restricted representation `Rep.res S.subtype A` has the same underlying
coefficient module as `A`; an element `s : S` acts by `A.ρ s.1`. Restriction
of `c` is therefore the function `(s, t) ↦ c (s.1, t.1)`. The hypothesis is
the explicit existence of a subgroup one-cochain `a : S → A` such that

`c (s.1, t.1) = (d₁₂ (Rep.res S.subtype A) a) (s, t)`

for all `s, t : S`. The right side is
`A.ρ s.1 (a t) - a (s * t) + a s`.

The conclusion uses a single `b : G → A` and requires both equalities

`c (s.1, g) = (d₁₂ A b) (s.1, g)` and
`c (g, s.1) = (d₁₂ A b) (g, s.1)`

for every `s : S` and `g : G`. These say exactly that subtracting the
boundary kills both kinds of mixed pairs. The proposition does not require
`b` to extend a specified subgroup primitive.

## Inflation injectivity

`Langlands.Cohomology.H2InflationInjectivity` states
`Function.Injective (groupCohomology.HInfRes A S 2).f` under the common
vanishing hypothesis. It isolates the first conclusion of
`H2InflationRestrictionExactness`.

Mathlib's `HInfRes A S 2` is the short complex

`H²(G/S, A^S) → H²(G, A) → H²(S, A)`.

Its first map `.f` is induced by the quotient homomorphism
`QuotientGroup.mk' S` and the inclusion of invariant coefficients into `A`.
The quotient representation is `A.quotientToInvariants S`.
The target asserts injectivity of this actual map; exactness at the middle
term remains part of the parent target.

## Source correspondence and internal provenance

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979, Chapter VII, section 6, Proposition 5, printed
pages 117–118 / PDF pages 123–124. Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 145 read these original pages. No project errata entry for this
source was present when checked.

Serre's normal subgroup `H` is named `S` here. Proposition 5 gives
inflation–restriction exactness in degree `q` assuming vanishing of subgroup
cohomology in degrees `1` through `q - 1`. The text on printed page 118
explicitly identifies the `q = 2` hypothesis as `H¹(H, A) = 0`.
`H2InflationInjectivity` is the immediate source-derived substatement
asserting injectivity of the first map for `q = 2`.
Serre uses group modules; forgetting the scalar structure of a `k`-linear
representation gives such a module with the same underlying additive
cochains, differentials, and inflation map. Retaining the scalar structure
does not impose an additional cohomological hypothesis.

`H2RelativeCocycleNormalForm` is an internal derived normal-form lemma
supporting Serre VII.6 Proposition 5, not a verbatim theorem in that source.
Serre proves his result by dimension shifting. The internal target instead
isolates an explicit-cochain step for a subsequent proof of the parent
exactness statement: adjust a cocycle with coboundary restriction until
both mixed restrictions vanish, then descend the adjusted cocycle to the
quotient with invariant coefficients. This intended use explains the
target's provenance; no proof of the adjustment or descent is asserted in
this statement module. Proofs of both targets are separate obligations.
