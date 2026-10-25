# Shahidi's Theorem 5.1 over general nonarchimedean local fields

This module states the comparison of the actual local coefficient with the
JPSS gamma relation over every `IsNonarchimedeanLocalField`, including fields
of positive characteristic. Its four declarations are proposition definitions.
It proves no analytic theorem and assumes no comparison or existence theorem.

Worker 99 adapted Worker 11's published `LocalCoefficientGammaStatement`
interface, retaining its two normalization clauses and documented source
boundaries. The adaptation uses the published `LocalCoefficientGeneral` and
`GeneralPairGamma` relations and the field normalizations of
`GeneralJacquetStatements`. It does not change the earlier p-adic statement.

## Original sources and derivation

The main source is F. Shahidi, *Fourier transforms of intertwining operators
and Plancherel measures for GL(n)*, American Journal of Mathematics 106
(1984), 67–111. Registered source: `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Theorem 5.1, printed page 103, asserts existence of a normalization such that

\[
C_\chi(s,\pi_1\otimes\pi_2)
 =\omega_{\pi_2}(-1)^{\operatorname{rank}(\pi_1)}
   \epsilon'(s,\pi_1\times\widetilde\pi_2,\psi).
\]

Page 68 defines the primed factor by
`ε'(s,π×σ,ψ) = ε(s,π×σ,ψ) L(1-s,π̃×σ̃)/L(s,π×σ)`.
Thus the intended factor is the JPSS gamma factor. The second factor in
Theorem 5.1 is the smooth contragredient of `π₂`; the central character in
the prefactor is that of `π₂` itself.

Page 70 fixes a nonarchimedean local field, residue cardinality, normalized
absolute value and character of integer-ring conductor. Equations (0.1)–(0.3)
on page 72 define the intertwining and Jacquet integrals and the inverse
coefficient convention. Page 73 records their measure dependence.
Pages 75–77 give the equal-rank measure recipe. Page 78 explains stabilized
Jacquet integrals in that equal-rank discussion. Pages 102–104 define the
rank-order convention and state and prove Theorem 5.1. Section 4, pages
94–96, supplies a separate adjacent-rank normalization.

The other source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics 105 (1983), §2.12, printed
page 403: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Its smaller-rank-first factors are defined by reversing the pair. The
published `GeneralPairGamma` Markdown explains the resulting gamma
convention and its definitional specialization to the p-adic gamma relation.

The provenance here is derived. The field scope is the source's original
scope, while the decomposition into two proposition definitions, the
all-pairs coefficient relation, the general Borel interfaces, and the shared
scalar Jacquet measure are formalization choices inherited from the
published modules. The expanded quantifiers are not asserted to occur
verbatim in the source.

## The comparison relation

All declarations are in `Langlands.Shahidi`. The field `F : Type uF` has
`Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. Representation carriers `V₁,V₂`
are arbitrary algebraic complex modules in a common universe `uV`,
independent of `uF`. There is no carrier norm, finite-dimensionality,
unitarity or supercuspidality requirement.

`IsGeneralLocalCoefficientGammaComparison q ψ abv hopen ν π₁ π₂ ω μ μJ μJ'`
leaves the integer `q`, absolute value, open norm-one proof, Fourier measure,
central-character candidate and three radical measures explicit. It says
there exist rational functions `C,G : RatFunc ℂ` such that:

1. `IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C`;
2. `IsGeneralSymmetricGammaFactor q ψ abv ν π₁ (smoothContragredient π₂) G`;
3. `C = ((ω (-1) : ℂˣ) : ℂ) ^ (m+1) • G`.

The ranks of `π₁,π₂` are `m+1,n+1`. Scalar multiplication on `RatFunc ℂ`
is multiplication by a constant. Both relations use evaluation at `q^(-s)`.
The first is the actual coefficient relation on the induced space: it
requires nonzero standard Whittaker forms to exist and a common rational
coefficient for every nonzero pair. For each pair it supplies a right
half-plane, a nonzero source Jacquet witness, a nonzero coefficient and
nonvanishing denominator, and the equation on all actual sections

\[
\lambda_{\pi'}^{-s}(A(s,\pi,w)f)=C(q^{-s})^{-1}\lambda_\pi^s(f).
\]

The source Jacquet measure `μJ` and intertwining measure `μ` are on
`Matrix (Fin (n+1)) (Fin (m+1)) F`; the target Jacquet measure `μJ'` is on
the exchanged matrix space. The imported relation uses stable integrals
and the actual tensor flip to `λ₂ ⊗ λ₁`. It does not assert absolute
convergence of every Jacquet integral.

This comparison predicate alone imposes neither residue normalization nor
Fourier self-duality nor the central-character property of `ω`. Those
conditions are imposed by the two analytic statement definitions below.

## The two targets and their aggregate

Each component repeats the following quantifiers and hypotheses:

- `q` equals `Nat.card` of the residue field of
  `(ValuativeRel.valuation F).integer`;
- `abv` is a real absolute value, `ϖ : Fˣ` is uniformizing,
  `abv ϖ = (q : ℝ)⁻¹`, and `valuation x = 1 → abv x = 1`;
- `ψ` is a unitary additive character with `Conductor.HasIntegerConductor ψ`;
- `ν` is an additive Haar measure on the Borel structure of `F` and
  `HarmonicAnalysis.IsSelfDual ψ ν` holds.

The character is continuous and nontrivial by its type.
`HasIntegerConductor` states triviality on the valuation ring and equality
of its annihilator with that ring. The unit normalization derives
`hopen : IsOpenNormOne abv` via `isOpenNormOne_of_valuation`.
The canonical additive uniform structure and `NonarchimedeanRing` instance
are constructed locally from the given topology and valuation; they are
not extra hypotheses on `F`.

`GeneralLocalCoefficientGammaAllRanksStatement F` then quantifies all
`m,n : ℕ` and representations of `GL_(m+1)(F),GL_(n+1)(F)`.
It assumes `IsGeneric ψ m π₁`, `IsGeneric ψ n π₂`, and
`Classification.HasGLCentralCharacter F (n+1) π₂ ω`.
Genericity includes irreducibility, admissibility (hence smoothness), and
a nonzero standard Whittaker functional. The character condition means
the scalar matrix associated to `c : Fˣ` acts as `ω(c)`.

The conclusion supplies `νI,νJ : AdditiveHaarMeasure F` and the comparison
with measures
`rectangularMeasure νI (n+1) (m+1)`,
`rectangularMeasure νJ (n+1) (m+1)`, and
`rectangularMeasure νJ (m+1) (n+1)`.
Thus one scalar Haar measure is shared by both Jacquet functionals.
The intertwining measure is chosen separately. Both choices occur after
the representations and may depend on them. They are not required to
equal the Fourier measure `ν`.

`GeneralLocalCoefficientGammaEqualRankStatement F` quantifies `n : ℕ`
with `0 < n`, representations of `GL_(n+1)(F)`, and the same genericity and
central-character hypotheses. It concludes existence of
`d : EqualRankMeasureData (ValuativeRel.valuation F).integer n` such that
`IsEqualRankGeometricNormalized ψ abv d` and the comparison holds with
`d.intertwining`, `d.jacquet`, `d.swappedJacquet`.
All measurable structures on the field, units, general linear groups,
upper unipotent groups, `KirillovQuotient`, integral subgroup and ambient
general linear group are their Borel structures.

`GeneralLocalCoefficientGammaStatement F` is exactly the conjunction of
these two targets at the same universe levels. No component is assumed.
All positive ranks, including rank one, occur in the first target; the
geometric refinement covers equal ranks at least two.

## Meaning and limits of the measure normalization

The equal-rank target reuses `IsEqualRankGeometricNormalized` from
`LocalCoefficientGammaStatement`. It retains the Haar and regularity
conditions; the unipotent product, quotient reflection and Weil composition
relations of item 1; the compact volumes of items 2–3; the Iwasawa formula
of item 4; the coordinate and Fourier conditions of items 2, 3 and 5; and
the actual radical pushforwards of items 6–7.
The imported `radical_coordinates` lemma identifies the intertwining
measure with the matrix-coordinate measure of item 5 and equates the
two Jacquet measures.

Only item 1's nonzero functional and its two Hermitian-pairing equations
are omitted from the geometric predicate. The published
`isEqualRankMeasureNormalized_iff` proves that adding them recovers the
full normalization. Those equations require a positive invariant form;
imposing them as hypotheses would restrict the final target to unitary
representations. Theorem 5.1 has no such restriction.

The earlier module's Markdown explains the remaining positive scale when
`0 < n`: geometric coordinate measures can be rescaled compatibly while
the intertwining measure changes, and the common Jacquet scale cancels
in the inverse coefficient equation. This scale argument is explanatory,
not a proof supplied by this module. At rank one the recipe degenerates:
the single self-dual coordinate pins the intertwining measure, so imposing
that recipe would strengthen the source's existential conclusion. The
geometric target therefore retains the published `0 < n` boundary.

For arbitrary unequal ranks the source has no uniform seven-item recipe.
Sharing `νJ` extends item 6 and the equality of the two Jacquet measures
in Section 4; it is a derived normalization. Any scalar rescaling
`μ ↦ a μ`, `μJ ↦ b μJ`, `μJ' ↦ d μJ'` changes `C` by `b/(ad)`.
The published coefficient relation contains the corresponding algebraic
scaling result. The explanation that every Haar measure on a positive
dimensional matrix space can be written as a scalar-product measure,
by taking an appropriate positive root of its scale, is not proved here.

Section 4's remaining adjacent-rank conditions are not stated here.
The stronger page-68 remark that the normalized measures can be chosen
independently of the representations is also not formalized. These are
retained source gaps, not additional hypotheses hidden in the comparison.

## Signs, Fourier transform and induction

Shahidi uses smaller-rank-first notation in (5.1), with the larger-rank
Whittaker function in the `ψ`-model and the smaller-rank function translated
by the alternating diagonal. The Library writes the larger rank first.
For `(π₁,π̃₂)`, the general symmetric relation uses `(π₁,π̃₂)` if `n ≤ m`
and `(π̃₂,π₁)` otherwise. Equal ranks keep the input order; no equal-rank
interchange theorem is proved here. In either branch the larger-rank
representation uses `ψ` and the other uses the inverse character.
The published `Signs` interface explains the alternating-diagonal
translation to the inverse-character model.

The Library's Fourier transform has the plus-sign kernel.
`IsSelfDual ψ ν` imposes its self-dual measure convention. The conjugate
kernel on source pages 76 and 80 is that same plus-sign transform with
the inverse character, as recorded by the imported coordinate predicates.
The geometric predicate imposes self-duality of the vector-coordinate
product, not of the matrix measure entry by entry; page 82 explicitly
distinguishes these.

The actual induction retains covariance exponents `(s+n+1)/2` and
`-(s+m+1)/2`. Its published Markdown documents the twice-halved display
on pages 67 and 72 and the interpretation supported by Lemma 2.2 on
page 84. That is an inference from the source, not an erratum.
The separate comparison of smooth sections with the source's
`K_r`-finite functions remains open.

## Proof boundary and checks

The intrinsic coefficient and gamma uniqueness results are imported from
`LocalCoefficientGeneral` and `GeneralPairGamma`; they require smoothness
and `1 < q` as appropriate. Genericity supplies smoothness, and the residue
cardinality is greater than one for a nonarchimedean local field.
This module chooses neither factor and proves no existence, convergence,
rational continuation, multiplicativity or comparison theorem.

The entry module compiles without errors or warnings. Exact inspection
of `GeneralLocalCoefficientGammaStatement` confirms a definition returning
`Prop`, with universe parameters `uF,uV` and only `propext`,
`Classical.choice`, `Quot.sound` in its axiom dependencies.
