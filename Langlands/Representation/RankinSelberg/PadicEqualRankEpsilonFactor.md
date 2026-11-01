# Constructed equal-rank p-adic epsilon factors

Author: Worker 31.

`padicEqualRankEpsilonData`, `padicEqualRankEpsilonFactor` and
`padicEqualRankEpsilonValue` construct, respectively, an element of
`ℂˣ × ℤ`, a unit of `RatFunc ℂ`, and a complex unit at every complex
spectral parameter. They apply to representations of the same positive rank
`n+1` over any p-adic field, including rank one. The field and both
representation carriers have independent universes. The supplied
`TopologicalData` determines the topology, normalized absolute value and
residue cardinality `q`. A nontrivial unitary additive character and a
self-dual additive Haar measure for its plus-sign Fourier transform are
supplied explicitly. The module does not choose a self-dual measure.

The first representation has full Whittaker type for the standard character;
the second has full Whittaker type for its inverse. This means admissibility,
finite type and a one-dimensional entire functional space. Irreducibility is
not required in the supplied-topology construction. The generic specialization
uses the canonical topology and the existing `Whittaker.IsGeneric` predicate,
which includes irreducibility, admissibility and a nonzero standard functional.

The original source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 0, printed p.378, fixes the self-dual Haar convention. Section 2.1,
printed pp.385–386, gives full Whittaker type and inverse-transpose dual
models. Theorem 2.7(iii), display (1), printed p.391 (retained PDF page26),
gives the equal-rank normalized functional equation. The source rank-minus-one
exponent is exactly `n` for rank `n+1`. Sections 2.9–2.10, printed pp.395–398,
explain monomial normalization and the Fourier comparison. These conventions
are inherited through the published full functional-equation theorem and the
existing epsilon relation. No new proof of the analytic equation is asserted.

The construction first proves `padicEqualRankEpsilonFactorExists`.
It obtains nonzero functionals from the two full-type hypotheses and applies
`equalRankFunctionalEquation` at the actual `unipotentQuotientHaar`, whose
compatibility has already been proved. The bridge
`exists_equalRankEpsilonEquation_iff` extracts one coefficient unit and
integer exponent before introducing any test vectors. The bridge
`equalRankEpsilonFactor_of_equation` transports that same equation to every
compatible quotient measure and every nonzero functional pair, using
compatible-measure uniqueness and equality of the Whittaker coefficient
models. Finally `isPairEpsilonFactor_self` identifies the equal-rank branch
of the existing pair relation. The resulting relation includes witnesses for
a compatible measure and nonzero functionals, so its universal clauses are
nonvacuous. The actual normalized integral families, Fourier transform,
inverse-transpose dual models, model-minus-one scalar and original/reflected
dual denominator conditions remain those of the existing relation.

The private `valuative_nonarchimedean` helper derives the nonarchimedean
additive structure from open submodules for the valuation topology. Explicit
`letI` telescopes install the supplied topology, local-field structure,
additive uniform structure and relevant Borel structures. This is a structural
bridge, with no additional mathematical assumption.

`padicEqualRankEpsilonData` applies the existing `pairEpsilonData` selector
to the proved existence result. Its specification is the full
`IsPairEpsilonFactor` relation for the original representations. Its equality
theorem compares it with every other certified coefficient/exponent pair,
using the proved residue-cardinality inequality `1 < q`.

`padicEqualRankEpsilonFactor` applies `pairEpsilonFactor` to the same proved
existence. Its coercion is exactly `C(c) * X^m`, where `(c,m)` is the selected
data and the formal variable is `X=q^(-s)`. The characterization theorem
identifies the unit with `rationalEpsilonMonomial` for any certified data.
The unit therefore comes from the actual integral relation and its proved
uniqueness.

`padicEqualRankEpsilonValue` applies `pairEpsilonValue` to the same data and
returns a complex unit for every `s : ℂ`. Its formula is the existing
`epsilonMonomial q c m s = c * (q^(-s))^m`. Positivity of `q` and the unit
coefficient give nonvanishing. The equality theorem gives the same formula
for any certified data. This module states rational and spectral formulas;
it does not add a general rational-function evaluation theorem.

`genericEqualRankEpsilonData`, `genericEqualRankEpsilonFactor` and
`genericEqualRankEpsilonValue` specialize these constructions to canonical
topological data. The canonical local instances have explicit module-specific
names so that the equal and unequal constructions can be imported together.
The published `GenericModel` bridges supply full standard
and inverse type using multiplicity one and character change. The generic
specification is exactly `IsPadicPairEpsilonFactor`. Its uniqueness and
rational/spectral characterizations reuse that intrinsic relation. None of
these constructors takes an analytic, functional-equation, epsilon-existence
or quotient-measure premise.

This is derived assembly of the published
[EqualRankFunctionalEquationProof](EqualRankFunctionalEquationProof.md),
[WhittakerGammaAdapters](WhittakerGammaAdapters.md),
[PairEpsilonFactor](PairEpsilonFactor.md),
[GenericModel](GenericModel.md) and
[PadicPairFactors](PadicPairFactors.md) APIs. Its explicit self-dual measure
and equal-rank scope are part of this construction. Unequal and reversed-rank
extensions, character transport, gamma factors, and classification-based
nongeneric factors are separate results.
