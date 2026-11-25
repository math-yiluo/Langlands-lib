# Actual finite-place norm twist in Harris's Proposition 4.8

`Langlands.Global.Harris.proposition48PlaceNormTwist.{uF}`
proves [`Proposition48PlaceNormTwistStatement`](HarrisParityLocalTransportStatement.md)
at its stated universe and hypotheses. The place datum `P` is arbitrary; the
proof does not require uniqueness of a place above it, general position, or an
algebraicity condition on the twisting character `ν`.

## Completion comparison and continuity

`placeCompletionEquiv` composes the upper completion map with `P.isoTilde`
and the embedding into the common algebraic closure. The range equality in
`P.IsCompatible` makes its corestriction a ring equivalence
\(E'_{v'}\simeq F'\). At the base, `P.iso` followed by the inverse of
`IntermediateField.botEquiv` identifies \(E_v\) with the bottom intermediate
field \(B\). `CompletionTower.completionMap_comp` compares the two maps from
\(E_v\) to the top completion; that identity is proved by agreement on the
dense copy of \(E\). With the other compatibility clause it gives the
commuting square over \(E_v\simeq B\). `Algebra.norm_eq_of_equiv_equiv`
transports the determinant norm across this square, and `Units.ext` gives the
comparison on field units.

The place isomorphisms are given as ring equivalences, not continuous maps.
The ideal membership of \(p\) gives residue prime \(p\) at \(v\), and the
lies-over relation gives the same prime at \(v'\). `padicFieldAt` packages
each completion over \(\mathbf Q_p\) without changing its carrier;
`completion_topology_eq` identifies its canonical topology with the native
completion topology. On a canonical p-adic field the normalized discrete
valuation is an ordered reparametrization of the canonical valuation, so its
unit ball is the spectral norm's unit ball. Its valuation ring is Henselian
by maximal-ideal-adic completeness.

For a prime \(\ell\) larger than \(p\) and the orders of \(p\) in both
fields of a comparison, `integral_iff_exists_pow` detects integrality of
\(x\) by the existence of a root of \(Y^\ell-(1+px^\ell)\). If \(x\)
is integral, \(1\) is a simple residue root: the value at \(1\) is in the
maximal ideal and the derivative there is the unit \(\ell\). If \(x\)
has negative order, then \(px^\ell\) has negative order, which is also
the order of \(1+px^\ell\). This order is congruent to the positive order
of \(p\) modulo \(\ell\), so it cannot be the order of an \(\ell\)-th
power. In Lean the latter calculation uses the logarithm of the discrete
multiplicative valuation (the negative of the additive order).

A ring equivalence preserves the equation in both directions and hence
preserves the closed unit ball. The multiples of this ball by \(p^n\) form
a neighborhood basis at zero, since \(0<\lVert p\rVert<1\); the proof
uses `Metric.nhds_basis_closedBall_pow` and tests membership by dividing by
\(p^n\). This gives continuity at zero and thus everywhere. Applying this
argument to the inverse comparisons gives the continuous unit maps needed
for character transport.

## Corrected component and the ambient Weil character

The witness `η'` is the finite component of
\(\xi\cdot(\nu\circ N_{E'/E})\) at \(v'\), composed with the inverse
upper comparison on units. Equality in the common algebraic closure in
`PlaceDatum.HasComponent` is exactly the equality of upper unit images needed
to verify this witness. For any \(y\in F'^\times\), take its preimage in
\(E'_{v'}{}^\times\). On that preimage, `HeckeCharacter.finiteComponent_mul`
and `HeckeCharacter.normComp_finiteComponent` compute the new value as the
old value times the base component evaluated on the local norm. By the
commuting norm square this is \(\eta(y)\mu(N_{F'/B}(y))\), with \(\mu\)
the transported \(\nu_v\) on \(B^\times\).

The witness `ψ` is the continuous composite of `Correspondence.baseWeilEquiv`,
`reciprocityUnits` for \(B\), and \(\mu\). On \(W_{F'}\), the first map
rebrackets the subgroup inclusion with the same underlying Weil element.
`LocalFactor.NonabelianSystem.DeligneHenniart.reciprocityUnits_weilInclusion`,
applied to the supplied normalized family, identifies the restricted value
with the norm factor. This proves the pointwise equality for the two actual
Weil characters. The proof constructs `ψ` at the specified place, not one
character common to different places.

## Provenance

This is the derived finite-place comparison described in
[`HarrisParityLocalTransportStatement`](HarrisParityLocalTransportStatement.md).
It adapts the range, norm and pointwise reciprocity calculation of
[`HarrisProposition48ExactStabilizerParityInheritanceProof`](HarrisProposition48ExactStabilizerParityInheritanceProof.md),
which assumes the corrected component is already given and uses only the
underlying multiplicative map of the auxiliary twist. Here both continuous
characters are constructed.

The motivating source is Michael Harris, *The local Langlands conjecture for
GL(n) over a p-adic field, n < p*, Invent. Math. **134** (1998), 177–210:
printed p. 200 fixes the compatible completion identifications, Definition 4.5
and Proposition 4.8 on p. 201 use the local characters, and the induction on
p. 202 uses a global norm pullback. The continuity and ambient-twist comparison
proved here is not a verbatim assertion in the paper. Registered source
[`harris-1998-local-langlands`](https://arxiv.org/abs/math/9611226), PDF SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
