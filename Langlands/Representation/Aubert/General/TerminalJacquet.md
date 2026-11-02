# Terminal cokernels and the associated-Levi Jacquet comparison

Full-smooth proposition targets by Worker 194. The elementary conversion of
a conjugate subgroup equality to a membership equivalence follows Worker
165's proof in the separate finite-length Jacquet target. The actual
subgroup functors and support predicate are due to Workers 23 and 379.

## Source and scope

The source is Aubert's 1996 erratum, printed p.4690, Remark (1), from the
definition of `D̃_G(E) = E#` through display (**). Its quantifier is every
smooth `E ∈ Alg({I})`. No finite-length, admissibility or irreducibility
premise appears in any declaration of this file.

The targets use the supplied standard-subset subgroup families, actual
semidirect decompositions, closed radicals and Levis, unimodularity,
increasing parabolics and decreasing radicals. The Levi-in-Levi
decompositions and their unimodularity hypotheses remain explicit.
`supportObjects I` is the object property defined by
`IsInSupportCategory ... I`, on the category of all smooth complex
representations in an arbitrary universe containing the group and index
universes. Its `ObjectProperty.ι` is the inclusion of the full subcategory;
its morphisms are all actual equivariant maps between those objects.

`JacquetCuspidalStatement` records the separate support-theoretic obligation
that `r_I(E)` is cuspidal in `M(I)` for such `E`. This assertion is not
assumed in the construction of a complex and is not an external structural
hypothesis.

## The two comparisons

`FixedLeviComparisonStatement` requires a natural isomorphism

`D̃_{M(I)} ∘ r_I ≅ r_I`

on the full support category of type `{I}`. The Levi cokernel is the actual
`LeviComplex.sharpFunctor` with the full Levi index as its support subset,
so it retains degree zero. Cuspidality of `r_I(E)` is the separate target
above; no vanishing condition is built into the object.

`AssociatedLeviComparisonStatement` is display (**):

`r_I ∘ D̃_G ≅ Ad(n) ∘ D̃_{M(I')} ∘ r_{I'}`.

Here `w_I` is the constructed `RelativeWeylIndexing.longestRep actual I` in
the actual relative Weyl quotient, and
`I' = RelativeWeylIndexing.associatedSubset actual I` is the simple image of
`I` under `w_I⁻¹`. The target quantifies over every normalizer lift `n` of
that element. The named structural prerequisite
`actualAssociatedLeviConjugation` identifies
`n M(I') n⁻¹ = M(I)`. Its elementary membership consequence supplies the
actual continuous `conjugationFunctor`, whose action is
`x ↦ σ(n⁻¹ x n)`.

`D̃_G` is `StandardComplex.sharpFunctor ... I`. On the other side,
`D̃_{M(I')}` is `LeviComplex.sharpFunctor ... Finset.univ`, the cokernel at
the full-Levi support rank. Both Jacquet functors are the normalized actual
coinvariant constructions. The ambient endpoint identities `P(S) = G` and
`U(S) = 1` are explicit parameters of the associated-Levi target.

The natural isomorphisms, rather than just isomorphisms of individual
objects, express compatibility with all maps in the support category.
This is the intended functorial form of the source calculation: the
complex maps, incoming images, quotient maps, Jacquet maps and conjugation
maps are the already constructed canonical ones. Proving this stronger
form requires proving that the corrected filtration comparisons and
surviving-grade identifications commute with those maps. `Nonempty`
requires the existence of the complete natural isomorphism, including
inverses and naturality squares; the declarations supply no such proof.

## Remaining obligations

These are proposition targets on explicit actual subgroup data, not
theorems about every generic nested family. A general reductive
specialization must realize the standard families and topology, the
Weyl-association relation used by the support predicate, the actual
Coxeter system, its longest-representative subset laws and the named
associated-Levi conjugation prerequisite in the shared Renard framework.
No split or quasisplit hypothesis is added. The empty index type and
relative semisimple rank zero are permitted.

The representation-theoretic proof must use the corrected two-sided
supports and prior double-coset minimality of Ban–Jantzen 2016, Section 4,
printed pp.161–162, actual graded Jacquet comparisons and their canonical
transition squares. A finite Weyl indexing set does not constrain the
length of `E`. Proposition 3.2 of Aubert 1995 remains unresolved, and its
incorrect proof is not a justification for any target here.

This file defines no Grothendieck-class equation. Its propositions have no
classification premise, but the transitive module imports do reach
classification modules; no classification-independence claim is made.
The class-level equation in the paragraph following (**) additionally needs
finite length of `E#` and the Euler class formula. Any later use of
Ban–Jantzen Proposition 4.1(3), printed p.158, must record that passage's
Langlands-classification dependency.
