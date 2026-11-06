# Actual Jacquet structure supplied by normalized temperedness

This derived supporting construction combines published pointwise geometry,
Jacquet admissibility and characteristic-space splitting
for the embedding step of Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 edition, VII.2.6, printed p.231 / PDF p.237
(registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
Its route uses the compatible root presentations already required by the
published normalized-exponent temperedness predicate. It does not establish
unconditional existence of those presentations.

The field and representation-carrier universes are independent. The ambient
rational points use their canonical topology with the stated local compactness
and nonarchimedean-group instances. The parabolic, rational Levi, split
component, geometric radical and multiplication isomorphism are the actual
specified data throughout.

`isAdmissible_jacquetFunctor_obj_of_presentation` starts with a supplied
compatible root presentation and an admissible source. The presentation's
split-component cocharacter identifies the literal Levi image with its dynamic
centralizer. `range_comp_radical_eq` identifies the supplied radical's literal
image with the dynamic identity-limit group. The published
`dynamic_hasOppositeIwahoriContractionBasis` supplies the opposite contraction
basis. Rewriting its radical and Levi subgroups and applying the published
normalized-Jacquet admissibility theorem proves admissibility of the actual
coinvariant quotient with its inverse-half-modulus normalization.

`IsNormalizedExponentTempered.isAdmissible_jacquetFunctor_obj` obtains that
presentation and source admissibility from temperedness.
`IsNormalizedExponentTempered.unitaryJacquetPart_isCompl` then applies the
published characteristic-space spanning result to obtain complementarity
of the unitary and nonunitary submodules. Neither requires a separate
Jacquet-admissibility or splitting hypothesis.

`IsNormalizedExponentTempered.radical_isUnimodularModulus` uses the same
presentation coverage and the published compact-containment result for its
literal radical. The existing theorem that a limit of compact subgroups
has trivial inner Haar modulus gives exactly the radical unimodularity
needed for normalized first adjointness.

`temperedLeviUnitaryJacquetRetraction` applies the published actual retraction
onto the unitary Jacquet module with complementarity derived by the preceding
lemma. Its companion identity proves that its composite with the literal
unitary-part inclusion is the identity. The Levi has `leviPointTopology`;
its affine structure, local compactness and nonarchimedean-group instance
are derived from the rational Levi witness and the closed Levi-point image.

This is a pointwise consequence of the existing temperedness definition,
not the unconditional global Jacquet-admissibility statement. It supplies
the splitting and radical-modulus inputs for the existing actual induction
embedding construction. Quotient compactness, a minimal parabolic with nonzero
unitary part, temperedness and square-integrability of a selected irreducible
quotient, and the uniqueness and unitarizability arguments remain separate
obligations. None of the three unconditional VII.2.6 propositions is proved
by this pair.
