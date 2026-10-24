# Fixed-vector constituent induction: proof

Worker 196 authored this proof and the induction design. Worker 166 authored
the semisimple base-case helpers it imports, and Worker 285 the finite-index
ascent theorem. Worker 283 prepared this pair for submission.

The theorem `Langlands.CuspidalSupport.fixedVectorConstituentInduction` proves
the published proposition
`Langlands.CuspidalSupport.FixedVectorConstituentInduction.{uG, uV}` from
`Langlands.Representation.CuspidalSupport.ConstituentInductionStatement`,
keeping the group and carrier universes independent. It has no theorem-valued
parameters and no additional hypotheses. The argument follows
Bernstein–Zelevinsky, *Representations of the group GL(n,F) where F is a
non-archimedean local field (survey)* (1976), Proposition 3.30, proof steps
(2) and (3), printed/PDF page 37, and Lemma 2.9(a), printed/PDF page 17
(registered source `bernstein-zelevinsky-1976-representations-gln`). The source
argues about an admissible representation of a Levi group; this proof uses only
the hypotheses of the published proposition, so it never assumes that `A` is
finite dimensional or admissible.

## Setting

`G` is a topological group, `H` a normal subgroup whose join with the center
has finite index, and `K` a compact open subgroup contained in `H`. The smooth
complex representation `A` is semisimple after restriction to `H`, and its
`K`-fixed vectors generate that restriction and form a finite-dimensional space.
The irreducible admissible representation `D` has a nonzero `K`-fixed vector
and is an actual subquotient of `A`. The conclusion is an actual injective
intertwiner from `D` to `A` and an actual surjective intertwiner from `A` to
`D`.

## The nonscalar step

The private theorem `constituentInduction_nonScalarStep` handles a central
element `z` and a scalar `c` such that `z` acts on `D` by `c` but not on `A`.
Its recursive hypothesis is the desired conclusion for every representation
whose `K`-fixed space has smaller dimension and which satisfies the same
semisimplicity, generation and finiteness hypotheses.

The central shift `A(z) - c` is the actual intertwiner `centralShift A z c`
from the ancillary module `CentralShift`. `centralShift_fixedVectors_descent`
shows that its actual kernel, image and cokernel all have `K`-fixed spaces of
strictly smaller dimension. The kernel and image are subrepresentations of `A`,
and the cokernel is a quotient. Their `K`-fixed spaces are finite dimensional:
the first two embed into the fixed space of `A`, and the third is the image of
that fixed space by compact averaging (`Compact.fixedVectorSurjectivity`).
`SmoothRep.semisimple_fixedVectors_generate_subquotient` gives each of them
semisimplicity over `H` and generation by its own `K`-fixed vectors.

By `irreducibleSubquotient_kernel_or_image`, `D` occurs in the kernel or the
image. The recursive hypothesis gives an embedding into that representation,
and composing with its inclusion into `A` gives the embedding of `D`. By
`irreducibleSubquotient_image_or_cokernel`, `D` occurs in the image or the
cokernel. The recursive hypothesis gives a surjection from that representation,
preceded either by the surjective corestriction of the shift onto its image
(`rangeFactor`) or by the cokernel projection.

## Reduction to a scalar counterexample

`constituentInduction_reduction` proves, under the same hypotheses, either the
two maps for `A` or the existence of a representation `B` that is semisimple
over `H`, on which every central element acts by a scalar, in which `D` occurs,
and for which the two maps do not both exist. It does not claim that `B` is
related to `A`. If such a `B` exists, the second alternative holds. Otherwise,
Schur's lemma for admissible irreducible representations
(`admissibleSchur_centralCharacter`) gives the central character `χ` of `D`,
and strong induction on the dimension of the `K`-fixed space proves the first
alternative for every representation with the hypotheses of `A`. In the
inductive step, if every central `z` acts by `χ z`, the representation would
be an excluded scalar counterexample. Otherwise some central `z` acts
differently and the nonscalar step applies, with the induction hypothesis as
its recursive hypothesis.

## Excluding the scalar counterexample

The closing theorem applies the reduction to `A`. In the second alternative,
the counterexample `B` has scalar central action and is semisimple over `H`.
`semisimple_sup_center_of_scalar` makes it semisimple over the join of `H` and
the center, which is normal with finite index.
`finiteIndexSemisimplicityAscent` (BZ76 Lemma 2.9(a), by averaging an
equivariant projection over cosets) makes `B` semisimple over `G`. Then
`constituent_of_semisimple` splits the actual subquotient presentation and
constructs both maps for `B`, a contradiction. Only the first alternative
remains, which is the conclusion.

## Imported results

The proof imports by Lean name the published statement, the central-shift
descent lemmas (`Langlands.Representation.CuspidalSupport.CentralShift`, submitted
with this proof), generation inheritance
(`Langlands.Representation.Smooth.FixedVectors.GenerationInheritance`), the
kernel/image/cokernel dichotomies
(`Langlands.Representation.Category.ConstituentDichotomy`), the semisimple base
case (`Langlands.Representation.CuspidalSupport.ConstituentSemisimple`) and
finite-index ascent (`Langlands.Representation.Category.FiniteIndexSemisimplicity`).
