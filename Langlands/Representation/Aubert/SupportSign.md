# The support adjustment on actual exact GL K₀

This module constructs the additive support-sign adjustment of Aubert,
Definition 2.1, printed p.2184, in the existing actual upper-parabolic,
right-translation GL conventions. The coefficient field is ℂ. The local field
is the current `PadicField p` model with independent field universe `uF` and
representation universe `max uF uV`; the full general local-field comparison
remains with the general-adapter sibling.

`supportSign_of_support` identifies the constructed sign with
`(-1)^(n - B.length)` for every actual irreducible quasicuspidal Levi module
whose normalized induction has the irreducible in question as a subquotient.
The sign is not chosen from a label-only model. Its existence uses an actual
quasicuspidal embedding, with signed effectivity on its actual constituents;
its uniqueness follows because involutivity makes each irreducible image
nonzero and a nonzero integer vector cannot be both effective and negative
effective. Rank zero uses the published actual identity rather than invoking a
positive-rank support theorem.

`adjustedOperator` is a ℤ-linear endomorphism of the **actual exact**
finite-length Grothendieck group. The intermediate genuine irreducible lattice
is transported through the published inverse Jordan–Holder realization and
factor-count maps. All actual short exact sequence relations, including
nonsplit ones, remain in that group. `adjustedOperator_irreducible` is its
precise defining formula; `adjustedOperator_rankZero` proves the identity on
the entire degree-zero group. No ring multiplicativity or whole Zelevinsky
comparison is asserted by this module. It is a focused construction step of
the larger specialization task.

## Sources and dependencies

The registered source is `aubert-1995-duality`, Definition 2.1 and Remark 2.2,
printed p.2184. The effectivity characterization is an internal construction
proved equivalent to the printed support sign, rather than a quotation of a
source definition. The imported GL results are reused without modification:
`alternatingOperator`, `alternatingOperator_rankZero`,
`alternatingOperator_injective`, `signedEffectivity`, and the actual
quasicuspidal-embedding and Jordan–Holder comparison declarations. The import
also exposes `irreducibleImage`, whose construction and proof are not changed.

More precisely, `irreducibleAubertVector_ne_zero` uses
`SmoothRep.IrreducibleOperator.onIrreducibles_injective` and
`alternatingOperator_injective`. The latter applies the published
`involutivity` to every exact class. `exists_effectiveSupportSign` uses
`CuspidalSupport.normalizedQuasicuspidalEmbedding`,
`normalizedInducedFiniteLengthObject`,
`mem_support_compositionFactors_of_injective`,
`mem_support_compositionFactors_iff_isSubquotient`, and `signedEffectivity`.
The construction needs no prior choice or uniqueness theorem for cuspidal
support. `supportSign_of_support` uses only signed effectivity and the proved
uniqueness of an effective sign. `adjustedOperator` uses
`VirtualRepresentation.extend` and
`SmoothRep.IrreducibleGrothendieckProof.factorMap`; its rank-zero identity
uses `realize_comp_factorMap`. These are genuine exact-class transports.

The signed-effectivity dependency includes the corrected two-sided support
filtration and complex proof, not the withdrawn proof of Aubert Proposition
3.2. The positive-rank support embedding depends on minimal nonzero Jacquet
descent, actual normalized induction and finite-length machinery. The
involutivity dependency passes through the geometric lemma and formal
induction/Jacquet identities. In particular, the actual induction K₀ owner
uses `Classification.normalizedInductionFiniteLength`. Its irreducible-Levi
case uses actual admissible product-Levi factorization and
`Classification.irreducibleProductFiniteLength`; that theorem uses
`irreducibleProductEmbedding`, the quasicuspidal tensor and induction-length
results, and ordered product regrouping. Thus the absence of a classification
premise in this module's types is no claim about transitive independence.
The broader source/dependency unit must track these helpers as well as any
segment or monomial classification used by the whole-ring comparison.

No arbitrary-local-field adapter, ring multiplicativity, polynomial basis,
whole-ring involution or general Renard Chapter V boundary is certified here.
Those are separate obligations of the specialization program.
