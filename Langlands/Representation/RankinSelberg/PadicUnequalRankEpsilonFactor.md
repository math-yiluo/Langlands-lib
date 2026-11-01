# Constructed unequal-rank p-adic epsilon factors

Worker 31. This module constructs the actual coefficient and exponent,
rational-function unit, and everywhere nonzero spectral value of the epsilon
factor of a pair of positive unequal ranks. It proves the published intrinsic
pair relation, then specializes the construction to generic representations.
The constructors require a supplied scalar Haar measure self-dual for the
specified additive character. Their analytic and epsilon-existence obligations
are discharged by published theorems.

## Parameters and normalization

The field is `F : PadicField p`, with `p` prime, and has arbitrary universe
`uF`. In the first API, `T : F.TopologicalData` is supplied. Each declaration
explicitly installs its topology, valuation and local-field structure, the
additive uniform structure, and the Borel measurable structures. The private
`valuative_nonarchimedean` proof derives the nonarchimedean additive structure
from the open-submodule basis for the valuative topology. The resulting total
disconnectedness supplies the shared Fourier self-duality predicate; this
bridge adds no assumption.

The representations `pi` and `sigma` act on the actual groups
`GL_(r+1)(F)` and `GL_(n+1)(F)`, on complex modules with independent universes
`uV` and `uW`. The rank assumption is `n < r`. Thus the smaller rank one,
`n = 0`, is included. The first representation has full Whittaker type for
the standard character of `psi`; the second has full Whittaker type for the
inverse standard character. This means admissibility, finite generation over
the group algebra, and a linear equivalence of the full functional space with
`Complex`. Irreducibility is not assumed in this API.

The scalar Haar measure `nu` and the proof `IsSelfDual psi nu` are supplied.
The same measure determines all rectangular product measures in the
unequal-rank integrals. The residue cardinality is `q = T.residueCardinality`,
the absolute value is `normalizedAbsoluteValue T`, and the rational spectral
variable is `X = q^(-s)`. The construction retains the shared plus-sign Fourier
self-duality normalization. It does not choose a self-dual measure or assert
that one exists for every character.

## Existence and the defining relation

`padicUnequalRankEpsilonFactorExists` proves the existing proposition
`PairEpsilonFactorExists` for these data. Its proof proceeds as follows:

1. `IsOfWhittakerType.exists_ne_zero` supplies nonzero functionals for both
   representations, without adding a chosen functional to the API.
2. The published `unequalRankFunctionalEquation` is applied at
   `unipotentQuotientHaar F.Carrier n`, using the published compatibility proof
   and the supplied self-dual scalar measure. Its full conclusion already
   chooses one coefficient and exponent before every allowed block.
3. `exists_unequalRankEpsilonEquation_iff` exposes the coefficient `c` and
   integer exponent `m` of that conclusion.
4. `unequalRankEpsilonFactor_of_equation` transports this same monomial to
   every compatible quotient measure and every nonzero functional pair.
   That published bridge uses uniqueness of the normalized quotient measure
   and equality of coefficient models for nonzero Whittaker functionals.
5. `isPairEpsilonFactor_of_lt` places the result in the existing pair relation.

Consequently the result has the full nonvacuous specification: a compatible
quotient measure exists, both functional spaces contain a nonzero element,
and the normalized functional equation holds for every compatible measure
and nonzero functional pair. Within each such equation, the same monomial
works at every `j,k` satisfying `r = n + (j+k+1)`.

The inherited equation retains the actual complementary dual block,
inverse-transpose models, inverse additive character and right translation
by the block Weyl matrix. It includes the normalized generator pair and the
rational continuations of the actual integrals, on the denominator domain of
`NormalizedFunctionalEquation`. The model-minus-one scalar and its power `r`
remain separate from the epsilon monomial. No central-character sign is
absorbed into `c` by these definitions.

## Actual data, rational unit and spectral value

`padicUnequalRankEpsilonData` applies the published `pairEpsilonData` selector
to the proved existence result. It returns `(c,m) : Complexˣ × Int`.
`padicUnequalRankEpsilonData_spec` proves the full `IsPairEpsilonFactor`
relation, and `padicUnequalRankEpsilonData_eq` identifies these data with any
other witness. The uniqueness proof uses the proved inequality `q > 1`.

`padicUnequalRankEpsilonFactor` applies `pairEpsilonFactor` to the same
existence result and self-duality proof. It is an actual unit of
`RationalFunctions = RatFunc Complex`. Its coercion theorem gives
`C(c) * X^m`; its characterization theorem equates it to
`rationalEpsilonMonomial e.1 e.2` for any certified epsilon data `e`.
The unit construction supplies its inverse and nonvanishing.

`padicUnequalRankEpsilonValue` applies `pairEpsilonValue`, returning a complex
unit at every `s`. Its formula is `epsilonMonomial q c m s`, namely
`c * (q^(-s))^m`. The value characterization gives the same formula with
any certified data. Nonvanishing follows from the existing monomial theorem
and the positive residue cardinality. The rational and spectral formulas
are proved separately; no additional rational-function evaluation theorem
is asserted here.

## Canonical generic specialization

`genericUnequalRankEpsilonData`, `genericUnequalRankEpsilonFactor` and
`genericUnequalRankEpsilonValue` install the field's canonical topology and
specialize the supplied-data construction to `F.canonicalTopologicalData`.
The canonical local instances have explicit module-specific names so that
the equal and unequal constructions can be imported together.
Their representation hypotheses are only `Whittaker.IsGeneric` for `pi`
and `sigma`. The published generic-to-full-type bridges supply standard and
inverse Whittaker type, using proved multiplicity one and character change.
The rank inequality and self-dual scalar measure remain explicit inputs.

`genericUnequalRankEpsilonData_isPadic` proves the existing
`IsPadicPairEpsilonFactor` relation. Thus its nonvacuity and universal
specification are retained. The generic uniqueness, rational coercion and
characterization, and spectral coercion and characterization theorems
specialize the corresponding facts above. All APIs retain the three
independent universes.

## Source and derived provenance

Registered original: `jpss-1983-rankin-selberg`, H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367–464. Retained PDF SHA256:
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.1, printed pp.385–386, supplies full Whittaker type.
Theorem 2.7(iii), display (2), printed p.391 (retained PDF page 26), gives
the unequal-rank epsilon monomial independent of the block. The scalar
self-dual Haar convention appears in the notation, printed p.378.
These original passages were read in this branch; p.391 was visually
reread for this construction and the source hash reverified.

This is a derived construction consuming the published proof
`unequalRankFunctionalEquation`, the fixed-monomial uniformity bridge in
`WhittakerGammaAdapters`, the selectors and units in `PairEpsilonFactor`,
and the type bridges in `GenericModel`. The local proof organizes existential
selection, uniqueness and specialization; it does not duplicate the analytic
proof of the functional equation or reuse an unpublished proof draft.

This focused unit covers `n < r`. Equal-rank and reversed-rank constructors,
change of character, twists, gamma factors and nongeneric Langlands products
remain separate parts of the broader task. It asserts no completion of them.
