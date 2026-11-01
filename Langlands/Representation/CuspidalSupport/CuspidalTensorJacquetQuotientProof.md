# Proof of actual cuspidal tensor Jacquet quotient existence

Author: Worker 78.

`Langlands.CuspidalSupport.cuspidalTensorJacquetQuotientExistence` proves the
published proposition
`Langlands.CuspidalSupport.CuspidalTensorJacquetQuotientExistence.{uF,uV} F T`.
For each positive rank and irreducible smooth representation, it constructs a
standard upper block shape and an actual external tensor of actual
supercuspidal block representations that is a quotient of the normalized
Jacquet module. The result preserves the supplied compatible topological data
`T` and independent field and carrier universes. The block factors and input
have carriers in `max uF uV`.

This is an internal derived construction from the published lower results
named below. It does not translate a support-set assertion into an actual
occurrence. The proof constructs a surjective equivariant linear map onto the
external tensor itself. It asserts no common twist line, unitarization,
integral-word existence, or classification, and uses no analytic hypothesis.

## Implemented construction

Install the topology and group structure selected by `T`. Irreducibility makes
the input `π` nontrivial, using
`QuasicuspidalEmbedding.nontrivial_of_isIrreducible`. Apply
`minimalNonzeroJacquet` to obtain a block shape `B` whose normalized upper
Jacquet module `J` is nonzero and Levi-quasicuspidal. The latter means that
every proper standard refinement has zero coinvariants.

Choose a nonzero vector of `π`. Its group orbit spans `π` by irreducibility.
Compactness of the parabolic quotient
(`Parabolic.parabolicQuotientCompact`) and
`QuasicuspidalEmbedding.exists_finset_generating` give finitely many vectors
generating `J` as a representation. The nonzero finitely generated module
therefore has a maximal proper subrepresentation `S`
(`exists_isCoatom_subrepresentation`).

Retain the actual quotient `σ = SmoothRep.quotient J S` and its canonical
surjection `q = SmoothRep.mkQ J S`. The quotient-kernel calculation and
`isIrreducible_of_isCoatom` show that `σ` is irreducible. Surjectivity of `q`
passes zero refinement coinvariants from `J` to `σ`, by
`coinvariants_subsingleton_of_surjective`, so `σ` is Levi-quasicuspidal.
Consequently
`LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility` supplies its
admissibility.

Apply `padicLeviCuspidalFactorization` to this actual irreducible admissible
Levi-quasicuspidal object. It supplies actual supercuspidal representations
`C i` and a representation equivalence `e` from `σ` to their external
tensor. Its universe parameters are explicitly
`{uF, max uF uV, max uF uV}`. The final quotient morphism is
`SmoothRep.ofHom (e.toIntertwiningMap.comp q)`. It is surjective because
`e` is bijective and `q` is surjective. This supplies exactly the
`SmoothRep.IsQuotient` in the target.

The proof reuses the finite-generation and maximal-quotient part of
`normalizedQuasicuspidalEmbedding_of`; it stops before Frobenius reciprocity.
Keeping that quotient avoids having to recover an actual tensor quotient from
an embedding into induction.

## Dependency and independence audit

The direct proof imports are the proposition module,
`QuasicuspidalEmbeddingProof`, `QuasicuspidalLeviAdmissibilityProof`, and
`LeviTensorFactorizationProof`, all under
`Langlands.Representation.CuspidalSupport`. The main mathematical inputs have
the following scope.

| Input | Construction used and independence boundary |
| --- | --- |
| `minimalNonzeroJacquet` | Maximizes the number of blocks of a nonzero Jacquet module. Refinement composition and the actual coinvariant quotient show that proper refinements vanish. It uses no support classification. |
| Compact parabolic quotient and `exists_finset_generating` | The compact quotient and a spanning orbit give finitely many Jacquet generators. The maximal quotient is ordinary module theory. |
| `irreducibleQuasicuspidalLeviAdmissibility` | Compact-open projections, vanishing across sufficiently large Cartan gaps, and the countable-dimensional Schur argument establish admissibility. No segment or multisegment result is used. |
| `padicLeviCuspidalFactorization` | Finite admissible product factorization constructs an external tensor; reflection of refinement coinvariant vanishing gives supercuspidality of each factor. `SmallRealizationProof` preserves the required independent universes. |
| Lower block and geometric coordinate lemmas | The factorization import chain includes block association and conjugating-coset constructions. Their role is finite block indexing and tensor transport, including `length_pos_of_pos`; they do not supply a classification or a one-line support theorem. |

The conservative project-source import closure was checked recursively from
this proof, including every project import of every imported module, against
the Library base `04247de81e81d501f4b57b138c70ba2d5b16e793` and the authored
statement pair. It comprises 163 project modules. Every project import was
resolved. None of the excluded statement modules or declarations below
occurs anywhere in those Lean sources. This whole-module check is stronger
than checking only the imports named by the entry module; the mathematical
roles just described also exclude assuming the same conclusions under
different names.

| Excluded family | Task |
| --- | --- |
| Analytic segment classification | `aca8805b-054f-4d56-8045-12db7f623404` |
| Multisegment special-head exhaustion | `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` |
| Ordered strong-head existence | `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` |
| Ordered quotient coverage | `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` |
| Tempered-block uniqueness | `52e97845-36bb-457d-b76f-70753334b88c` |
| `SquareIntegrableLanglandsClassification` | `1cb45da2-7007-4351-a694-594fb148b8d1` |
| Square-integrable Langlands-head exhaustion | `cd8ab97c-0b78-4bce-97c4-d307a28159a4` |
| Regular tempered Langlands-head exhaustion | `bf433f0a-921a-428c-b0c0-6475438125ac` |

No proof successor can provide one of these excluded propositions through
this closure, since its statement and conclusion are absent. In addition, the
construction invokes no global disjoint-support irreducibility, general
ordered quotient coverage, full multisegment classification, or one-integral-line
support assertion. Twisting and normalized Jacquet constructions appear among
the lower imports, but this proof applies neither a local factor interchange
nor a Casselman comparison. Those remain separate inputs for any later proof
of integral-word existence.

Development compilation and theorem inspection succeed with only
`propext`, `Classical.choice`, and `Quot.sound` among the reported axioms.
This is a compilation and dependency account; independent review and
publication are separate from these development checks.
