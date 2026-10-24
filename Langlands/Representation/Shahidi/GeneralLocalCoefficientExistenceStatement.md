# Rational local-coefficient existence over general nonarchimedean local fields

This module states rational existence for the published
`Langlands.Shahidi.IsGeneralLocalCoefficient` relation on the actual induced
representation. It includes positive-characteristic local fields. Its two
declarations return `Prop`; neither supplies a proof of an analytic theorem
or chooses a coefficient without one.

## Source and derivation

The source is Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984), 67–111,
registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page 70 fixes the residue cardinality, normalized absolute value
and conductor of the additive character. Printed page 72 defines the
intertwining operator in (0.1), the Jacquet functional in (0.2), and the
inverse local-coefficient relation in (0.3); the display after (0.3) gives
the target functional. Printed page 73 records dependence on the three
measures. Printed page 78, (1.1) and its following paragraph, explains the
stable-integral reading of the Jacquet functional in the equal-rank section.

The provenance is derived: this is the general-field adaptation of
`PadicField.TopologicalData.ShahidiLocalCoefficientExistenceStatement`
in `JacquetStatements`, using the actual relation in
`LocalCoefficientGeneral` and the normalizations in
`GeneralJacquetStatements`. It expresses the analytic obligation implicit
in (0.3), with rational dependence encoded by the already published
relation. It does not claim that all of its expanded quantifiers occur
verbatim in one source display. In particular the all-pairs formulation
uses the published relation quantified over every nonzero pair of standard
Whittaker forms, rather than selecting the source's fixed pair.
The published fixed-form-to-all-pairs lemma requires multiplicity one.

Worker 99 made this adaptation. Worker 11 contributed to the earlier
statement interface and normalization discussion. The imported general
relation and its intrinsic lemmas are Worker 33's published work.

## Exact existence statement

The namespace is `Langlands.Shahidi`. The field has `Field F`,
`ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F` instances, with no characteristic
restriction. The Borel measurable structure is installed on `F` before
the measures are quantified. The rank indices `m,n` encode positive
ranks `m+1,n+1`.

`GeneralLocalCoefficientExistenceStatement F m n` quantifies over:

- `q : ℕ` equal to the cardinality of the residue field of the valuation
  ring;
- an absolute value `abv : AbsoluteValue F ℝ`, a uniformizing unit `ϖ`,
  the equation `abv ϖ = (q : ℝ)⁻¹`, and the normalization
  `valuation x = 1 → abv x = 1`;
- a unitary additive character `ψ` with `Conductor.HasIntegerConductor ψ`;
- three arbitrary fixed additive Haar measures `ν,νJ,νJ'` on `F`;
- arbitrary algebraic complex carriers `V₁,V₂` in a common universe
  independent of the field universe, and representations `π₁,π₂` of
  `GL_(m+1)(F),GL_(n+1)(F)` on them.

The unit normalization supplies `hopen : IsOpenNormOne abv` by
`isOpenNormOne_of_valuation`, so smoothness of the determinant twists is
derived from the field normalization. `HasIntegerConductor` says that
`ψ` is trivial on the valuation ring and its annihilator is precisely
that ring. `Whittaker.IsGeneric ψ m π₁` and
`Whittaker.IsGeneric ψ n π₂` include irreducibility, admissibility and
existence of a nonzero standard Whittaker form. There is no norm,
finite-dimensionality, unitarity or supercuspidality assumption on the
carriers or representations.

For such data, the conclusion is existence of `C : RatFunc ℂ` satisfying
`IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C`, where:

- `μ = rectangularMeasure ν (n+1) (m+1)` is the intertwining measure;
- `μJ = rectangularMeasure νJ (n+1) (m+1)` is the source Jacquet measure;
- `μJ' = rectangularMeasure νJ' (m+1) (n+1)` is the target Jacquet measure.

These are measures on the two actual rectangular radical coordinate
spaces, as in the source's (0.1), (0.2), and the target formula.
They are fixed before the representations and coefficient are quantified.
No equality between them, self-duality, or comparison normalization is
imposed. This statement concerns existence for independent Haar choices;
their coupling for Theorem 5.1 is a separate obligation.

The imported relation requires nonzero standard forms on both factors and,
for every such pair, a right half-plane on which `C(q^(-s))` has a nonzero
denominator, a section has a nonzero source Jacquet value, and all actual
sections satisfy the intertwining/Jacquet relation with nonzero
`c = C(q^(-s))`:

\[
\lambda_{\pi'}^{-s}(A(s,\pi,w)f)=c^{-1}\lambda_\pi^s(f).
\]

The half-plane may depend on the pair of forms. The rational function is
the same for all pairs. The relation uses stabilized Jacquet integrals,
not asserted absolute convergence over the entire radical. The tensor
flip identifies the generic target functional with the literal
`λ₂ ⊗ λ₁` on `I(-s,π₂ ⊗ π₁)`, as proved in the imported relation module.

The underlying induction retains the normalized exponents
`(s+n+1)/2` and `-(s+m+1)/2`. Its documented interpretation of the
twice-halved display on source pages 67 and 72, using Lemma 2.2 on page 84,
and the open comparison between smooth and source `K_r`-finite sections
are unchanged. This module introduces no induction construction.

## Combined target and proof boundary

`GeneralJacquetAndCoefficientStatement F m n` is the conjunction of the
published `GeneralJacquetStatement F m n` and the new existence statement.
The first conjunct is itself stabilization and induced Whittaker
multiplicity one. Thus all three analytic obligations are conclusions of
the aggregate target, with consistent universe parameters; none is
assumed as a hypothesis.

The algebraic result
`existsUnique_inverseScalar_of_multiplicityOne` in `JacquetStatements`
isolates the pointwise step: given a nonzero Whittaker form, a nonzero
pullback of the target form along an intertwiner, and multiplicity one,
there is a unique nonzero inverse scalar. It does not prove nonzero
pullback or rational dependence on `s`. The new existence target retains
both of those analytic obligations through `IsGeneralLocalCoefficient`.

Intrinsic uniqueness is already proved by
`IsGeneralLocalCoefficient.unique` for smooth factors and `1 < q`.
This module neither re-proves it nor adds a chosen coefficient.
It proves no analytic existence, stabilization, continuation,
multiplicity-one or gamma-comparison theorem.
