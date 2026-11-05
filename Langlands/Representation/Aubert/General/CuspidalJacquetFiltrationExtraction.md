# Cuspidal-factor extraction from supplied actual graded pieces

Authors: Workers 1553 and 321. Worker 321 identified the existing arbitrary-grade
extraction theorem and agreed the division between the actual Jacquet
subquotient reduction and this dependent-witness filtration argument.

This is an internal conditional assembly for task
`e6add7c5-44c5-45ea-afe9-7f48c98fb927`. It does not prove
`RationalCuspidalJacquetFactorExtractionStatement`. In particular it does
not construct a geometric filtration or prove that proper induced grades
exclude all irreducible inside-Levi cuspidal subquotients.

`CuspidalJacquetGradedPieces` is a proposition about a supplied finite
`ObjectRepFiltration s` of an actual smooth representation `A` of `M J`.
Every actual smooth grade must satisfy one of two alternatives:

- No irreducible `IsLeviCuspidal` representation of `M J` is an actual
  `SmoothRep.IsSubquotient` of the grade.
- There is a point `n`, a membership witness
  `hn : ∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`, an association
  `IsAssociate I J n`, and an actual smooth isomorphism from the entire
  grade to `(conjugationFunctor n hn).obj σ`.

This is an explicit input interface. Its association predicate is arbitrary;
there is no truth assertion for arbitrary subgroup families. It contains
no K0 relation and supplies no structural comparison.

`exists_conjugation_iso_of_finiteFiltration` uses the weaker alternatives
that each grade either excludes the single chosen irreducible `τ`, or is
an associated conjugate of the irreducible `σ`. Given
`SmoothRep.IsSubquotient τ A`, it returns an actual isomorphism
`τ ≅ (conjugationFunctor n hn).obj σ` for the same `n` and dependent `hn`
as the association and membership comparisons. It applies
`ObjectRepFiltration.exists_smoothGradedObject_subquotient` to choose a
grade containing `τ`. The exclusion alternative contradicts this
occurrence. In the other alternative it transports the occurrence along
the supplied grade isomorphism. Inverse conjugation preserves
irreducibility, so this occurrence between irreducibles is an actual
isomorphism.

`cuspidalJacquetFactor_of_finiteFiltration` specializes the uniform
exclusion in `CuspidalJacquetGradedPieces` to the supplied irreducible
inside-Levi cuspidal `τ`, then applies the preceding theorem. There is no
irreducibility assumption on `A`, and no admissibility, finite length or
finite generation assumption on any representation. The grades in the
exclusion alternative may be arbitrary. The length of the supplied
filtration may be zero; the extraction theorem makes an irreducible
subquotient of such a filtration impossible. The index type, group and
carrier universes remain independent; the complex carrier universe is
`max uG uV`, as in the generic extraction target.

## Implemented algebra and dependencies

The private lemma `iso_of_irreducible_subquotient` presents an actual
subquotient by an injective map `i : C ⟶ A` and a surjective map
`q : C ⟶ D`. Nonzeroness of the irreducible `D` makes `i` nonzero.
Irreducibility of `A` makes `i` surjective. Its inverse transports `q`
to a nonzero intertwiner `A ⟶ D` between irreducibles. This is
bijective, and its inverse gives the asserted isomorphism.

The declaration dependencies used by the new argument are:

- `ObjectRepFiltration.exists_smoothGradedObject_subquotient` from
  `Filtration.ActualGradedExtraction`, an elementary finite-filtration
  extraction for arbitrary actual grades.
- `SmoothRep.isSubquotient_iff_exists`,
  `SmoothRep.hom_hom_surjective` and
  `SmoothRep.IsSubquotient.of_iso_right` from
  `Classification.SupercuspidalSupport`, used only for actual
  injective/surjective presentations and transport under isomorphism.
- `Langlands.isIrreducible_comp_continuousMulEquiv_iff` applied to
  `conjugationEquiv n hn`, preserving the explicit inverse action
  `x ↦ σ(n⁻¹ * x * n)`.
- Mathlib's
  `Representation.IsIrreducible.surjective_or_eq_zero`,
  `Representation.IsIrreducible.bijective_or_eq_zero` and the
  nontriviality of a simple module.

The direct imports are the unchanged rational target and
`Filtration.ActualGradedExtraction`. The latter's classification-named
imports provide elementary range, kernel and quotient algebra; this
argument invokes no support existence, uniqueness or classification
theorem. The rational target's structural imports remain available but
the new argument does not discharge their hypotheses. No geometric lemma,
adjointness theorem or proper-induction exclusion is invoked as a proved
input here.

The provenance is elementary algebra applied to the extraction pattern
specified by the published target. Renard VI.5.3(ii),(iii) and the first
paragraph of VI.5.4 motivate that target, as documented in its unchanged
paired Markdown; this module claims no new formalization of those source
passages. Establishing the actual rational filtration, its exclusion and
conjugation alternatives, and the actual Jacquet occurrence remains
necessary before these helpers can prove the whole rational target.
