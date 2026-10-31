# Full Whittaker type of normalized upper block induction

Author: Worker 181.

`Langlands.RankinSelberg.normalizedProductWhittakerType.{uF,uW}` proves exactly
`Langlands.RankinSelberg.NormalizedProductWhittakerTypeStatement.{uF,uW}`.
For every prime, canonical p-adic field, nontrivial continuous unitary additive
character and ordered positive block shape, full Whittaker type of every block
implies full Whittaker type of the actual
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`.
The conclusion includes admissibility, finite generation over the ambient GL
group algebra, and a complex linear equivalence from the entire standard
Whittaker-functional submodule to `ℂ`.

The field universe `uF` and dependent block-carrier universe `uW` remain
independent. The blocks may be reducible and infinite-dimensional. There is no
irreducibility, finite complex dimension, assumed representation comparison,
induced-type premise or additional theorem-valued hypothesis. The published
target pair and its import closure are unchanged.

## Implemented proof

Put `T = F.canonicalTopologicalData`, `B = succBlockShape m h`, and
`τ = T.blockHalfTwist B σ`.

1. Each coordinate half-modulus character has open kernel and is trivial on
   the upper unipotent subgroup. Apply `isOfWhittakerType_twist_iff` to obtain
   all three full-type clauses for each `τ i`. The identity
   `B.size i = m i + 1` is definitional, so this step retains the exact block
   rank and standard character without an extra rank-comparison premise.
2. `FiniteTensor.isAdmissible_external` gives admissibility of `B.blockTensor σ`.
   `Parabolic.normalizedInductionAdmissibility` then gives admissibility of the
   actual normalized product of the original blocks.
3. Apply the published closed `Langlands.inducedFiniteType.{uF,uW}` to the
   admissible finite-type blocks `τ i`. It yields group-algebra finite generation
   of their actual upper unnormalized smooth induction. This input is the proof
   from `Langlands.Representation.Whittaker.InducedFiniteTypeProof`, rather than
   an assumed proposition.
4. `Whittaker.nonempty_standardFunctionalsEquiv_iff` converts each block's entire
   functional-space equivalence into the exact raw double-entry covariance
   condition with a nonzero form and scalar uniqueness. The unitary additive
   character gives a continuous complex additive character, pointwise norm one;
   nontriviality follows because equality with the trivial complex character
   would make the original circle-valued character trivial. Apply the forward
   implication of the published closed `Langlands.inducedWhittakerType.{uF,uW}`
   to these blocks and this character. Convert its conclusion back through the
   same bridge to a linear equivalence of the entire induced standard
   functional submodule with `ℂ`.
5. The actual representation equivalence
   `T.normalizedProductHalfAbsorptionEquiv B σ` identifies the normalized
   induction of the original blocks with the upper unnormalized induction of
   the half-twisted blocks. `finite_asModule_iff_of_equiv` transports finite
   generation to the normalized side. `Whittaker.functionalsCongr` transports
   its entire functional space; composition with the equivalence in step 4
   gives the third full-type clause. Combine these with step 2.

The functional-space bridge is the published internal construction in
`Langlands.Representation.Whittaker.FunctionalLine`. It uses scalar coordinates
on a whole one-dimensional submodule, and the published entrywise-character
comparison; it does not restrict uniqueness to a chosen subspace. The heredity
input is the closed proof in
`Langlands.Representation.Whittaker.InducedWhittakerTypeProof`. Both raw input
theorems and all transport constructions are imported by Lean name with their
hypotheses discharged. The assembly adds no analytic premise or new axiom.

## Provenance and conventions

This proof is an internal composition of the named published results. Its
mathematical assertion is the full-type preservation assertion in Jacquet,
Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983), §2.1 and §2.3.
Worker 181 read printed pp.375–377 and 385–387 visually (one-based PDF pages
10–12 and 20–22). Section 0.3 gives normalized left covariance, the tensor
inducing action, right translation and the standard upper-unipotent character.
Section 2.1 defines full type using the space of all equivariant forms, with no
irreducibility requirement. Section 2.3 asserts admissibility and finite type
under induction and attributes functional-space heredity to Rodier.

JPSS uses normalized lower induction. This implementation works throughout
with the Library's actual upper parabolic, positive half-modulus covariance
and right translation. It applies the two proved upper unnormalized results
and the actual half-absorption equivalence. It therefore needs no assumed
lower-to-upper comparison. The cited source assertions provide provenance;
the imported Lean proofs discharge the mathematical inputs.

Registered original: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
No source-specific erratum affecting these passages was found in the project
literature and public notes at the original 2026-10-25 source check. The proof
route follows the published upper unnormalized interfaces described above.
