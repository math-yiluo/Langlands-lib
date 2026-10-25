# Nonzero standard modules and conditional canonical heads

Author: Worker 156.

This module supplies a focused construction used by the regular tempered head
existence project. It does not prove
`Langlands.GLRegularLanglandsHeadExistenceStatement`. In particular, neither
finite length of parabolic induction nor exclusion of its two-irreducible
product quotients is established here.

The selected construction `canonicalIrreducibleHeadOfFiniteLength` takes a
nonzero smooth complex representation `A`, a proof of its finite group-algebra
length, and `NoIrreducibleProductQuotient A.representation`. It returns a smooth
representation together with the full `IsIrreducibleHead` relation from `A`.
The returned representation is definitionally `A.headQuotient`, as the
`canonicalIrreducibleHeadOfFiniteLength_val` lemma records. The relation includes
an actual surjective intertwiner and equality of its linear kernel with every
irreducible quotient kernel.

`NoIrreducibleProductQuotient` means that no intertwiner from the given
representation onto the actual product of two irreducibles is surjective.
The factors may be identical or isomorphic. Its target carriers have the same
universe as the source carrier; that universe is independent of the group
universe. This is the obstruction already used in the published
`IrreducibleHeadProductCriterionStatement`, named here for the constructor.

The helper `exists_irreducibleQuotient_of_finiteLength` first obtains
Noetherianity of the actual group-algebra module. The order isomorphism from
subrepresentations to submodules transfers coatomicity. A nonzero vector
excludes equality of bottom and top, so there is a maximal proper
subrepresentation. The actual smooth quotient by this subrepresentation is
irreducible by
`CuspidalSupport.QuasicuspidalEmbedding.isIrreducible_of_isCoatom`;
`SmoothRep.mkQ_surjective` supplies its quotient map.
`hasIrreducibleHead_of_finiteLength_noProduct` combines this existence witness
with the published `Classification.irreducibleHeadProductCriterion`.
The smooth canonical-head equivalence then certifies the selected construction.

For normalized product induction, `nontrivial_normalizedProductInduction`
requires only that each smooth block be nonzero. Choose a vector-space basis
for each block. A choice of indices gives a nonzero basis vector in their
actual finite tensor product, including the empty product case. Inflation to
the parabolic and twisting by the half modulus preserve smoothness.
`Induction.compactLocalSection` constructs a compact local section whose value
at the identity is this vector. Its image in the smooth induced carrier is
nonzero, since evaluation of a zero section would give zero. The proof uses
the existing nonarchimedean and locally compact topology of the actual GL group.
It does not require admissibility, irreducibility, or a classification theorem.

For a tempered Langlands datum, `twistedBlock_irreducible` uses invariance of
irreducibility under real determinant twist.
`twistedBlock_admissible_finiteLength` obtains admissibility from temperedness
and twist invariance, and finite length from irreducibility: a simple module
is Noetherian and Artinian. `standardModule_nontrivial` specializes the
nonzeroness construction to these blocks.
`standardModule_finiteLength_of_productPreservation` applies a supplied proof
of `AdmissibleFiniteLengthProductPreservation` at positive rank. That proposition
is an explicit hypothesis, not an imported proof.
Finally, `standardModule_hasHead_of_finiteLength_noProduct` specializes the
canonical-head construction to the actual standard module, retaining both
finite length and the product obstruction as hypotheses.

All these constructions are internal deductions from the published Library
definitions and lemmas and Mathlib's vector-space bases, finite tensor basis,
simple-module facts, and coatomic lattice structure. They assert no new claim
from external literature. The general smooth construction has independent
group and carrier universes; the GL specialization has independent field and
block-carrier universes, with the actual induced carrier in their maximum.
No strict-order assumption is used in these preparatory deductions. The
regular-chamber analytic and relative comparison arguments needed to discharge
the product obstruction remain separate obligations.
