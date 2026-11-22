# Isobaric strong multiplicity one from inducing-data and real parameter uniqueness

Getz–Hahn (2024), Corollary 11.7.3, p. 309 (one-based PDF p. 320),
state strong multiplicity one for isobaric automorphic representations.
`IsobaricStrongMultiplicityOneReductionStatement.{u,uQ}` gives a sufficient
condition for the unchanged Library formulation of that corollary. It
takes `CuspidalInducingDataRigidityStatement.{u,uQ}` and
`RealStandardIsotypicParameterUniquenessStatement.{u,u}` as premises.
The consequent retains every hypothesis of
`IsobaricStrongMultiplicityOneStatement.{u,uQ}` and yields an equivalence
for the finite adelic, compact and enveloping-algebra actions.
`isobaricStrongMultiplicityOne_of_rigidity_and_real_parameters` proves
the implication.

The proof unpacks the two isobaric witnesses. Outside the union of their spectral
exceptional sets and the given finite set, the normalized block inductions
have a common spherical subquotient. The common finite-place embeddings
identify the supplied local isobaric sums there. Applying the rigidity
premise to the common subquotient gives a bijection of the two families
with equal positive-rank cuspidal classes. This uses the local results of
Getz–Hahn, Theorems 10.6.3–4, pp. 285–286 (one-based PDF pp. 297–298),
and the rigidity of Theorem 10.7.2, p. 287 (one-based PDF p. 299).

At each finite place, local equivalence within matched classes and
Rodier's multisegment classification identify the two local isobaric
sums. The multisegment sum implements the local construction in
Getz–Hahn, §10.6, (10.33), p. 284 (PDF p. 296), using Rodier (1982),
§4.3, Theorem 3(b), pp. 211–212 (PDF pp. 12–13). Each of the two
finite-place embeddings then gives isotypy for the common local sum.

At each real or complex place, the matched cuspidal classes give
equal multisets of their respective block data. In the real case the
supplied parameter uniqueness for a common irreducible isotypic
restriction gives a permutation of the normalized Mœglin data
`realMoeglinData`. A nonzero induced weight contributes its absolute
value. A weight-zero block contributes the two real characters of the
same exponent. Knapp (1994), (3.2)–(3.4), pp. 402–403 (PDF pp. 412–413),
describes the Weil data and their correspondence with these blocks.
The Library's `realStandardModule_append_expand` implements equality
of the standard modules under the weight-zero expansion. In the
complex case the compact scalar-vector argument and parameter
uniqueness compare the lists of characters, using Knapp, (4.3) and
Theorem 4(a), (c), p. 405 (PDF p. 415). Reindexing the pooled data as
in Getz–Hahn, (10.33), p. 284 (PDF p. 296), gives a permutation at each
archimedean place. The ordered standard-module and quotient comparisons
then identify a common irreducible admissible type.

The real quotient and permutation comparisons use the Library's
determinant-exponent order, weakly decreasing `Re(t_j)`, as in
Getz–Hahn, (10.29)–(10.30), p. 283 (PDF p. 295), and Theorem 10.6.1,
p. 284 (PDF p. 296). Knapp's real classification in Theorem 1(a), (c),
p. 400 (PDF p. 410), has the corresponding quotient and permutation
conclusions, with (2.5) printed using `Re(t_j)/n_j` for the determinant
exponents of the rank-`n_j` blocks in (2.2). In the Library normalization
the root between adjacent blocks evaluates to `t_j - t_(j+1)`, giving
the Getz–Hahn order as the closed positive chamber. See
[IsobaricAutomorphicRepresentation, §2](IsobaricAutomorphicRepresentation.md#2-the-langlands-order-of-archimedean-blocks).

For the real quotient theorem, spherical cyclicity gives the scalar commutant
for tied lists without a nonzero-weight rank-two block. The published separated
and coincident cases give the scalar commutant for the other tied lists.
`realTemperedStandardIrreducible_of_form_of_scalarCommutant` uses the invariant
form to turn scalarity into irreducibility of the tied standard modules.
`realLeviLanglandsQuotient` then applies chart integrability and parabolic
integration to put every proper stable subspace in the kernel of a nonzero
linear functional. Their supremum is the largest proper stable subspace.
This establishes the real quotient assertion in the determinant-exponent
order using the same Library results as the quotient step in
`RealLargeLanglandsQuotientInjectiveProof`.

The resulting common admissible types give a full operator equivalence
by `nonempty_equivalence_of_common_admissible_localComponents`. The
isotypic restrictions implement the argument at the end of the proof of
Flath (1979), Theorem 1, p. 180 (PDF p. 176). The final equivalence uses
the cyclic evaluation form of his restricted-tensor uniqueness argument,
§2, Example 2, and §3, Theorem 3, pp. 181–182 (PDF pp. 177–178).

The implication is a derived formulation of the route in the paired
Markdown of the published target. It combines the local comparison and
determination steps while retaining the two inputs as proof arguments.
