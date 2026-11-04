# Reduction of actual cuspidal factor extraction to the induced object

Author: Worker 321.

This is an internal reduction for the actual extraction target authored by
Worker 76 with Workers 55, 379, 6, 8 and 14, whose existing Lean/Markdown pair is
imported unchanged. It implements the exactness step in the first proof
paragraph of Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Théorème VI.5.4, printed p.174/PDF p.180. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The direct-induced proposition and equivalence are derived proof organization,
not separate assertions in the source.

`InducedCuspidalJacquetFactorExtractionTarget` is a Prop-valued template
restricting extraction to actual irreducible cuspidal subquotients of
`r_J(i_I σ)`. It has the same cuspidality conditions and the same conclusion
as `CuspidalJacquetFactorExtractionTarget`: one element `n`, one dependent
Levi-membership witness `hn`, the association of the root subsets, and an
actual isomorphism to the inverse-conjugated datum, all using this same `n`
and `hn`. There is no general extraction theorem for arbitrary subgroup
families in this file.

`isSubquotient_jacquet_induction_of_exact` assumes that the actual normalized
Jacquet functors preserve all short exact intertwiner sequences. It applies
`Langlands.ExactSmoothTransport.map_isSubquotient` to the actual subquotient
relation `π ≤ i_I σ`, then composes with `τ ≤ r_J π` using
`Langlands.smoothSubquotientTransitivity`. Neither irreducibility nor finite
length of `π` is needed. The theorem does not replace any relation by an
equality in a Grothendieck group.

`cuspidalJacquetFactorExtractionTarget_iff_induced` proves the equivalence of
the two templates under that exactness hypothesis. Its forward implication
uses the whole induction as `π`, with identity injection and surjection.
Its reverse implication applies the preceding transitivity theorem before
calling extraction for the whole induced object. The representative and
dependent membership witness returned by extraction are passed through
unchanged.

`RationalInducedCuspidalJacquetFactorExtractionStatement.{u, v}` repeats the
displayed rational data of the published full extraction target, replacing
only its template by the direct-induced template. It retains independent
universes `u` and `v`, arbitrary nonarchimedean local fields including positive
characteristic, all connected reductive groups, canonical point topology, the
actual simple-root and standard subgroup families, and the full normalizer
modulo the centralizer. There is no restriction on splitness, quasisplitness,
relative rank, or the emptiness of the simple-root set.

`rationalCuspidalJacquetFactorExtractionStatement_iff_induced` is an
unconditional equivalence at this scope. Its only representation-theoretic
exactness input is the published
`RationalPointFamily.standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement`
from `RationalUnipotentRegularity`, which derives full actual normalized
Jacquet exactness from the displayed field, reductive group, torus, generic
cocharacter and `StandardCocharacterStatement` data. No additional compactness,
compact-limit, endpoint, finite-length, admissibility or finite-generation
hypothesis is introduced.

The subquotient characterization and its transport are imported through
`Langlands.Representation.Classification.SupercuspidalSupport`; the actual
declarations used are its algebraic `SmoothRep.isSubquotient_iff_exists` and
the exact-functor and transitivity theorems above. This proof invokes no
classification, adjointness or geometric-filtration theorem. The direct-induced
extraction assertion itself, including proper-induction exclusion and the
same-representative root/Levi/datum comparisons, remains to be proved.
