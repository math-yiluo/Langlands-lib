# Finite length under the actual normalized parabolic functors

Author: Worker 395.

`Langlands.Parabolic.normalizedParabolicFiniteLength.{uField,uCarrier} F T`
proves exactly
`Langlands.Parabolic.NormalizedParabolicFiniteLengthStatement.{uField,uCarrier} F T`.
Its outer parameters are `{p : ℕ} [Fact p.Prime]`, an actual
`F : PadicField.{uField} p`, and arbitrary supplied `T : F.TopologicalData`.
There are no additional mathematical premises.

The theorem is the conjunction of finite-length preservation by the existing
`T.normalizedParabolicInductionFunctor B` and `T.normalizedJacquetFunctor B`.
It includes every natural rank and ordered block shape, every smooth complex
representation of the actual product Levi or ambient GL group, and zero
representations. Length means `IsFiniteLength` over the actual complex group
algebra, as in `SmoothRep.HasFiniteLength`. No admissibility, finite generation,
irreducibility, positive rank, finite complex dimension, central character or
tensor-factorization assumption is added to the statement.

The constructions retain the supplied `T.topology`. Induction uses the upper
block parabolic, positive half-modulus covariance and right translation on the
actual smooth covariant functions. Jacquet uses the actual upper-unipotent
coinvariants and the inverse half-modulus twist. This module applies those
functors directly; it does not construct replacement functors or change their
normalization.

## Implemented induction argument

`FiniteLengthFunctorAssembly.normalizedInductionFunctorFiniteLength` splits
on the actual ambient rank.

In positive rank, the Levi conjunct of the published
`Langlands.finiteLengthAdmissibility` proves admissibility of the given smooth
finite-length object. The published
`Langlands.Classification.normalizedInductionFiniteLength` then proves finite
length of its actual normalized induction. Its input is the arbitrary original
Levi representation. No tensor factorization of that input is chosen here.
The helper's admissibility and positive-rank premises are discharged in the
proof, so neither is a premise of the closing theorem.

At rank zero,
`FiniteLengthFunctorAssembly.normalizedInductionFiniteLength_rankZero` gives
an elementary argument from the actual definitions. Positivity of every block
size and the shape's index equivalence imply that its block index set is empty.
The actual product Levi and `GL_0` are therefore trivial groups. The constant
identity homomorphism from `GL_0` onto the Levi is surjective.
`Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` transfers
finite group-algebra length from the input representation to its pullback
along that homomorphism. Evaluation at the identity is a complex-linear
intertwiner from the actual normalized induction to this pullback. Equivariance
follows because every ambient group element is the identity. Functions on
`GL_0` are determined by that value, so evaluation is injective.
`Langlands.FiniteLengthAssembly.finiteLength_of_injective` transfers finite
length to the induction. The character laws give value one at the identity;
no separate modulus comparison or finite-dimensional replacement is needed.
The proof includes the empty shape and the zero input.

## Implemented Jacquet argument

`FiniteLengthFunctorAssembly.finiteGeneration_of_finiteLength` extracts
Noetherianity from finite module length and infers finite generation over the
group algebra. The intermediate
`normalizedJacquetFiniteLength_of_admissible` combines this fact with the
published `Langlands.Parabolic.normalizedJacquetFiniteLength`. That theorem
accepts admissibility and finite group-algebra generation of the original GL
representation and concludes finite length over the actual product-Levi group
algebra of its normalized Jacquet module, for all ranks and arbitrary `T`.

`FiniteLengthFunctorAssembly.normalizedJacquetFunctorFiniteLength` discharges
admissibility using the GL conjunct of `Langlands.finiteLengthAdmissibility`.
It therefore proves the exact unconditional Jacquet clause for smooth
finite-length inputs. Finally, `normalizedParabolicFiniteLength` pairs the
induction and Jacquet clauses.

The field and input-carrier universes remain independent. The induction output
carrier has universe `max uField uCarrier`, and the Jacquet output retains
`uCarrier`. Evaluation in rank zero may connect these different universes.
The closing theorem explicitly orders its fresh universe parameters as field,
then carrier. The final examples specialize to `uCarrier := max uF uV` and
check both published `SmoothRep.PreservesFiniteLength` predicates. Universe
normalization makes the saturated induction output stay in the same carrier
universe; no resizing is used.

## Imported proofs and independence audit

The direct project imports are the unchanged
`Parabolic.FiniteLengthFunctorStatement`,
`Classification.FiniteLengthProof`,
`Smooth.Admissibility.FiniteLengthProof`, and
`Classification.NormalizedProductFiniteLengthProof`, all under
`Langlands.Representation`.

The positive-rank helper uses an actual Levi composition series. Each simple
quotient is admissible, factors into irreducible GL blocks by the published
Levi factorization theorem, and has finite-length induction by the published
irreducible-product theorem. Normalized induction exactness propagates length
along the series. The irreducible-product theorem in turn uses cuspidal
embeddings, injections of external tensors, consecutive ordered regrouping,
and finite length of cuspidal induction. The latter is obtained from associated
Jacquet filtrations, detection of nonzero subquotients, and the finite-family
length criterion. These are shared lower inputs, rather than segment or
multisegment classification.

The admissibility import uses finite-length module induction, irreducible GL
and Levi admissibility, and short-exact admissibility. The imported Jacquet
length theorem uses quasicuspidal decomposition, the quasicuspidal length
criterion and induction on proper refined Jacquet modules. Its arbitrary-`T`
Jacquet helper is used here; the separate canonical-topology GL conclusion
is not needed.

The combined transitive project import graph was audited at Library commit
`a9fae2951e0ea3e71a3319caba67d2b93350b350`. It has 596 project modules,
all with nonempty paired Markdown, and every imported pair agrees with that
Library. The exact target pair and all its imports are unedited by this
contribution. An older local baseline differs only in an already published
`Group/GL/BlockModulus.md` documentation update; no imported Lean source was
changed.

The audit read the eight excluded task objectives, inspected the mathematical
routes above and scanned every transitive project Lean source, including
imports, for their statement and proof names without case sensitivity. There
are no matches for analytic segment classification, special-head multisegment
exhaustion, ordered strong-head existence, ordered quotient coverage, tempered
block uniqueness, square-integrable Langlands classification, square-integrable
exhaustion, or regular exhaustion, including their named proof successors.
Neither those conclusions nor a theorem-valued replacement for finite-length
preservation is used. The newly proved assembly and rank-zero steps use only
the actual definitions and the named module-length transport lemmas.

## Source correspondence and provenance

This is an internal assembly of the published proofs above and elementary
module arguments. Its source correspondence is Casselman, *Introduction to the
theory of admissible representations of p-adic reductive groups*, draft of
1 May 1995. Corollary 6.3.8, printed/PDF p.60, gives finite length of normalized
induction for an admissible finite-length Levi input. The additional passage
from arbitrary smooth finite length to admissibility is provided by the
separately published admissibility theorem, not an omitted hypothesis of that
corollary. Theorem 3.3.1, printed/PDF p.35, preserves finite generation and
admissibility under Jacquet modules; Theorem 6.3.10, printed/PDF p.60, supplies
the corresponding general finite-length scope. The imported Jacquet theorem's
refinement-induction proof and source route are described in its own paired
Markdown. This file does not reproduce Casselman's proof of those results.

Sections 2.4 and 3.1, printed/PDF pp.26 and 32, give right translation and the
positive half-modulus convention for parabolic induction. These original
passages and pp.35 and 60 were read directly. The registered source is
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`,
retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
No source-specific errata note was present in the current public notes.
