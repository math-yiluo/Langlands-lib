# Rank-one Weil orbit counts

`Langlands.Henniart.weilRankOneCount.{uK,uW}` proves
[`WeilRankOneCountStatement.{uK,uW}`](HenniartWeilElementaryLayer.md) on the
Library's actual Weil twist-orbit strata. For a p-adic field \(K\) of residue
cardinality \(q\), the count is \(q-1\) at Swan exponent zero and
\((q-1)^2q^{s-1}\) at Swan exponent \(s\geq 1\). The field and representation
universes are independent.

This is Proposition `prop:rank1` of the operator route note
`operator-numerical-llc-route-2026-11-16`, §5.1 (`numerical-LLC-route.tex`,
lines 684–686). Henniart, *La conjecture de Langlands locale numérique pour
GL(n)* (1988), [§3.1, p. 507](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=12),
gives the cumulative rank-one count via the characters of \(K^\times\) trivial
on \(U^{j+1}\), modulo unramified characters. The proof below implements that
unit-quotient calculation, including the comparison with the Library's
finite-inertia Artin conductor.

## Conductor under reciprocity

Choose a geometric reciprocity map using `weilReciprocityTheorems` and pull a
continuous field character \(\chi\) back to a Weil character. In
`rankOne_presentation_conductor`, the kernel condition of a finite inertia
presentation makes the scalar character descend: evaluate the trivial line
action on `ULift.up 1`, then lift the scalar homomorphism along the surjective
restriction map. `ULift.moduleEquiv` identifies the resulting action with the
one-dimensional scalar action on \(\mathbb C\).

For real \(v\geq 0\), `trivial_upper_iff_finite` uses the absolute-to-finite
upper-group image theorem and the identification of Weil inertia with absolute
inertia. It equates triviality of the descended character on the finite upper
group with triviality on the Weil upper group. Upper reciprocity identifies the
image of the latter with \(U^{\lceil v\rceil}\). Thus the rank-one Artin-sum
lemma gives exactly the multiplicative conductor \(a(\chi)\), defined by the
unit filtration. `finiteInertiaConductorEquivalence` compares this computation
with any witness of `Numerical.HasArtinConductor` for the same class. Hence the
Swan exponent is \(a(\chi)-1\) with subtraction truncated at zero.

## Orbits and finite quotients

Every rank-one class comes from a field character. The geometric normalization
identifies the twist by \(z\) with multiplication by \(z^{\operatorname{ord}_K}\).
A twist fixing a character has \(z=1\), by evaluation at a uniformizer. Two
characters belong to the same twist orbit precisely when they agree on the
valuation units \(U^0\): if they agree there, their quotient is the unramified
character determined by its uniformizer value.

`rankOneBounded_encard` identifies the orbits of conductor at most \(m\) with
the complex characters of \(U^0/U^m\). A bounded character restricts and
descends to this quotient. Conversely, compose a quotient character with
\(x\mapsto x/\pi^{\operatorname{ord}_K(x)}\) followed by the quotient map; the
extension is continuous because it is trivial on the open subgroup \(U^m\).
Restriction to \(U^0\) recovers the quotient character, so the orbit map is
injective. The graded unit equivalences identify \(U^0/U^1\) with the
multiplicative group of the residue field and \(U^i/U^{i+1}\) for \(i>0\) with
its additive group. Multiplicativity of relative index gives
\(|U^0/U^{n+1}|=(q-1)q^n\). Finite abelian duality gives the same size for its
complex character group.

Finally, all the rank-one classes have torsion number one. The Swan-zero
stratum is the set of orbits of conductor at most one. For positive Swan
exponent \(s\), the stratum is the difference between the sets bounded by
\(s+1\) and by \(s\) in conductor. Additivity of `Set.encard` and cancellation
of the finite smaller count in `ℕ∞` give \((q-1)^2q^{s-1}\). No higher-rank
correspondence or count is used.
