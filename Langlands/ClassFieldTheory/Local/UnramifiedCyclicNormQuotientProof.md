# The topological cyclic quotient for unramified norms

Worker 84 proves `Langlands.LocalClassField.unramifiedCyclicNormQuotient.{u,v}`
with exactly the published type
`Langlands.LocalClassField.UnramifiedCyclicNormQuotient.{u,v}`.
For every prime, compatible finite extension of p-adic fields in independent
carrier universes, and supplied topological data `T,S` with equal absolute
ramification indices, put `d = Module.finrank F.Carrier E.Carrier`. The theorem
constructs a continuous multiplicative equivalence

\[
F^\times/N_{E/F}(E^\times)\ \simeq_{\mathrm{top}}\
\operatorname{Multiplicative}(\mathbb Z/d\mathbb Z)
\]

whose value on the class of `a` is
`Multiplicative.ofAdd (T.ord (a : F.Carrier) : ZMod d)`.
The source is the published `NormQuotient`, with the actual quotient topology
induced by `T.topology` on field units. The cyclic target has the discrete
topology stipulated in the statement. The theorem retains every original
quantifier and hypothesis, including degree one.

## Implemented proof

The private helper `ord_units_locallyConstant` proves that normalized order
is locally constant on field units. At a unit `a`, the nonzero sphere of the
canonical valuation restricted to its value group is open. Its inverse image
under the continuous inclusion of units is an open neighborhood of `a`.
Equality of the restricted valuation implies equality of the canonical
valuation by its value-group embedding. The definition of normalized order
then gives constant order on this neighborhood.

The private homomorphism `orderMod T d` sends a unit to its normalized order
modulo `d`, viewed multiplicatively. The identities for order at one and at
products prove the homomorphism laws. `orderMod_surjective` first lifts a
`ZMod d` element to an integer and then uses `T.ord_surjective_nonzero` to
realize that integer as the order of a nonzero field element. Converting that
element to a field unit supplies the required preimage.

The closing theorem imports `unramifiedNormMembership` from
`Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof`. That
published theorem and `ZMod.intCast_zmod_eq_zero_iff_dvd` identify the actual
norm subgroup with the kernel of `orderMod T d`. The proof composes
`QuotientGroup.quotientMulEquivOfEq` with
`QuotientGroup.quotientKerEquivOfSurjective`. This supplies the algebraic
equivalence; its required value formula on quotient classes holds by
definition.

Local constancy of order implies local constancy, and hence continuity, of
its reduction modulo `d`. The universal property of the quotient topology,
expressed by `QuotientGroup.isQuotientMap_mk`, transfers this continuity to
the induced equivalence. Its inverse is continuous because its domain is
the discrete cyclic target. These two facts form the continuous
multiplicative equivalence. No discrete topology is installed on the source.
The same construction handles degree one without a separate case.

## Provenance and dependencies

This is the derived normalized-order and topological formulation of
Jean-Pierre Serre, *Local Fields*, Greenberg English translation, GTM 67
(1979), Chapter V, Section 2, Proposition 3(c), printed p.82/PDF p.89,
together with the preceding unit-norm propositions, corollary and
finite-residue-field remark. Worker 84 read PDF pp.88–89. The valuation
quotient in the source gives the cyclic group; the topology argument here
is the explicit deduction from open valuation spheres and the quotient
topology. The private helpers implement this deduction.

Registered source: `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
No source-specific errata file was found in the project notes.

The norm-membership theorem was authored by Worker 90 and is independently
accepted and published. It imports the published norm-order and unit-norm
proofs by Worker 110 and Worker 26. This module imports their declarations;
it does not copy their proofs. The normalized-order API is imported from
`Langlands.LocalField.Normalization.Proof`. The statement pair and all
imported pairs are unchanged. The result adds no Galois, norm-membership
or reciprocity assumption and makes no Frobenius or reciprocity assertion.
