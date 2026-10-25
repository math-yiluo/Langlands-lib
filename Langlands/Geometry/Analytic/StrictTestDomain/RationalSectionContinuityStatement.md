# Continuous orbits on a fixed rational section algebra

Author: Worker 36.

`RationalSectionOrbitContinuityStatement` is a proposition definition.
It states a target for the constructed action on a rational quotient;
this module supplies no Lean proof of the target.

Let `K` be a complete ultrametric normed field, `P` an actual presented
strict affinoid `K`-algebra, and `d : RationalData K P` a unit-radius
rational presentation. Let `G` be a topological group and let
`ρ : G →* locusStabilizer d` be a group homomorphism. The codomain
is the actual setwise stabilizer of `d.locus` under inverse algebra
pullback on the spectrum. In particular, the hypothesis preserves the
subset without requiring preservation of its chosen presentation or
fixation of individual points.

Assume that every forward base-algebra orbit
`g ↦ (ρ g).hom(a)` is continuous in the norm topology on `P`.
The target asserts that for every `b : d.algebra` the orbit
`g ↦ (stabilizerSectionAction d (ρ g)).hom(b)` is continuous in
the quotient norm topology on the actual rational algebra `d.algebra`.
Here the section action is the constructed forward bounded algebra
action: it compares with the moved quotient and restricts back to the
fixed quotient. On a base section it sends `d.baseMap(a)` to
`d.baseMap((ρ g).hom(a))`. This convention agrees with the existing
left spectrum action by inverse pullback, and multiplication applies
the right factor first.

The field and group occupy independent universes. Completeness is
required for the existing rational quotient and action construction.
No nontrivial valuation, reducedness, nonzero quotient, nonempty locus,
positive numerator arity, or local compactness of `G` is assumed.
There is no topology on `Aut P` or on `locusStabilizer d` in the
statement, and `ρ` is an algebraic homomorphism with the displayed
orbit-continuity hypothesis. In particular, neither a common operator
bound nor continuity of the desired section orbits is supplied as a
premise.

This is an internally derived local continuity criterion. A proposed
proof first uses the structural base-map equation to obtain continuity
on the old presentation coordinates. The image of the denominator is
a unit in the rational quotient. Continuity of inversion on units and
the equations `d.baseMap(d.denominator) * d.fraction(j) =
d.baseMap(d.numerator(j))` then give continuity on the fraction
coordinates. At the identity, all these quotient-coordinate images
have norm at most one. Their finite number and the ultrametric
inequality give a neighborhood where the images still have norm at
most one. Convergent Tate evaluation and the quotient norm then give
a common local bound on the section operators. Polynomial
approximation extends continuity to every section at the identity;
the action law and boundedness of each fixed operator extend it to
all group elements. A zero quotient can be treated separately.
These are proposed proof steps, not results proved in this module.
In particular, individual boundedness alone is not used as a claim of
a common bound on the whole group.

The underlying constructions come from Berkovich,
*Non-archimedean analytic spaces*, Trieste lectures (2009):
the quotient norm and strict affinoid presentations in section 2.1
and Definition 2.1.2, printed/PDF p. 7; bounded morphisms in
Definition 2.1.11, p. 8; and rational domains and their quotient
algebras in Definition 2.2.1 and Exercise 2.2.2(ii), p. 9.
The criterion above is derived from these constructions and the
Library's actual fixed-quotient action. It is not quoted as a numbered
theorem of that source. Registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces* (1995-1996), section 1.1, printed/PDF pp. 1-2, motivates
continuity on local functions: its analytic automorphism topology
uses preservation of compact analytic domains and bounds on finitely
many functions there. The present target is limited to norm-continuous
orbits on one invariant rational quotient. It does not construct or
identify that automorphism topology, prove openness of the stabilizer,
give a full analytic action or an equivariant etale site, or assert
that section stabilizers are open. The source uses spectral bounds
on functions; the target deliberately asserts continuity in the
constructed quotient norm, without identifying that norm with a
spectral norm.

The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
