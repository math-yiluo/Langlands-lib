# Canonical p-adic gamma construction

Worker 31. This module assembles the published equal- and unequal-rank gamma
constructors, specializes them to the canonical realization of a p-adic field,
and returns an actual rational-function unit with the existing universal gamma
relation. The final constructor covers either order of two positive ranks,
including rank one. Analytic conclusions, epsilon existence, self-duality and
four Whittaker-type hypotheses remain explicit inputs.

## Sources and derived provenance

Jacquet--Piatetski-Shapiro--Shalika, *Rankin--Selberg Convolutions* (1983),
Theorem 2.7(ii)--(iii), printed p.391, gives normalized reciprocal-polynomial
L factors and the equal- and unequal-rank epsilon equations. Algebraically
rearranging these equations gives the gamma expression used by the imported
constructors:

\[
 G(X)=\epsilon(X)\frac{L^\vee(q^{-1}/X)}{L(X)}
     =cX^m\frac{P(X)}{P^\vee(q^{-1}/X)}.
\]

The central-character sign stays outside this expression. For the ranks
`r+1` and `n+1` used in Lean its exponent is `r`. The complementary rectangular
indices satisfy `r = n + (j + k + 1)`. The imported unequal-rank equation retains
the block-Weyl right translation and uses the dual block `k,j`.

JPSS Section 2.12, printed p.403, defines L and epsilon factors of a pair in
reversed unequal-rank order by putting the larger rank first. The published
`IsPadicSymmetricGammaFactor` uses the resulting gamma convention. JPSS does
not separately give a gamma convention in that paragraph; it follows from the
ratio above and preservation of ranks by duality. In equal rank the Lean
relation keeps the input order. This module does not prove equal-rank exchange.
Both original pages were visually read in `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

Folland, *A Course in Abstract Harmonic Analysis*, second edition (2015),
Section 2.6, Proposition 2.50 and Theorem 2.51, printed pp.62--63, formula
(2.52), supplies the quotient integration normalization. The fixed ambient
and subgroup Haar measures determine the invariant quotient measure exactly.
Those pages were read in `folland-2015-abstract-harmonic-analysis-second`,
SHA256 `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The published `UnipotentQuotient` module already constructs the normalized
measure for the left quotient `N \\ GL`, using unimodularity and the opposite
quotient convention via inversion. This module consumes that construction and
its compatibility theorem; it proves no new quotient-measure theorem.

This is a derived assembly of `EqualRankGammaFactor`, `UnequalRankGammaFactor`,
`PadicPairFactors`, and the existing p-adic topology and measure interfaces.
The new input propositions organize explicit hypotheses. They do not assert
the analytic results or epsilon existence. The constructors use only published
factor relations and return data with proved fields.

## Parameters and analytic input

The field and the two representation carriers have independent universes
`uF`, `uV`, and `uW`. Representations are complex-linear, with no requirement
that their carriers be finite dimensional. The ranks are `r+1` and `n+1` for
natural numbers `r,n`.

`PairAnalyticInput q psi abv mu nu pi sigma` is a proposition. In equal rank,
after transport along `r = n`, it asks for `EqualRankAnalyticConclusion` for
every pair of nonzero standard/inverse-standard Whittaker functionals. This
conclusion contains the published Schwartz-test analytic family. In unequal
rank it asks for `UnequalRankAnalyticAt j k hr` for every nonzero functional
pair and every natural `j,k` with `hr : r = n + (j + k + 1)`. The rectangular
measure is exactly `rectangularMeasure nu j (n+1)`. No restriction excludes
`j = 0`, `k = 0`, or `n = 0`. If `r < n`, the unequal branch has no admissible
blocks; the constructors therefore separately require `n ≤ r`.

The analytic conclusions include convergence on a right half-plane, rational
continuation, a common denominator and normalized-generator existence for
the relevant coefficient models. `PairAnalyticInput` makes no additional
assertion that these properties hold. For the dual pair the module uses
`inverseTransposePullback pi` and `inverseTransposePullback sigma` with
`psi.scale (-1)`. The dual input quantifies over all their nonzero Whittaker
functionals. This is a sufficient hypothesis stronger in form than an input
restricted to the particular constructed dual functionals. The assembly
specializes it using `firstDualFunctional_ne_zero` and
`secondDualFunctional_ne_zero`.

`gammaFactorOfAnalyticInput` works over a nonarchimedean local field with its
valuative relation and topology, Borel measurable structures on the field,
smaller general linear group, upper unipotent subgroup and left quotient,
and Hausdorff and totally disconnected field topology. It takes `q > 1`, an
absolute value, a self-dual additive Haar measure, a quotient measure compatible
with the fixed `generalLinearHaar` and `unipotentHaar`, and `n ≤ r`. It also
takes original and dual `PairAnalyticInput`, `PairEpsilonFactorExists`, and
four `IsOfWhittakerType` hypotheses: the original standard/inverse-standard
pair and the dual pair for the scaled character. Whittaker type retains the
published admissibility, finite-generation and one-dimensional functional-space
conditions. Nonzero functionals are supplied through epsilon existence.

The constructor splits on equality of ranks, specializes the dual analytic
input, and applies `equalRankGammaFactor` or `unequalRankGammaFactor`. It
returns a subtype of `RationalFunctionsˣ` whose property is exactly
`IsPairGammaFactor`. The published constructors derive the intrinsic original
and dual L-polynomials from the supplied hypotheses; this module asks for no
separate intrinsic L-polynomial existence input. Their universal equations and
full common reduced-denominator domain are preserved unchanged, including
points where zeros cancel in the displayed polynomial expression.

## Canonical p-adic specialization

`PadicPairGammaInput F psi nu pi sigma` installs the canonical topological
data of `F : PadicField p`, where `p` is any prime. It uses the associated
residue cardinality, `normalizedAbsoluteValue`, and Borel structures. Its
quotient measure is `unipotentQuotientHaar F.Carrier n`. The input is the
conjunction of `n ≤ r`, self-duality, epsilon existence, the four Whittaker-type
hypotheses, and the original and dual analytic inputs at this constructed
quotient measure.

The topology certificates are obtained rather than assumed. The published
`TopologicalData.fieldT2` supplies Hausdorffness. The private helper
`valuativeTotallyDisconnected` transports Mathlib's
`ValuativeRel.nonarchimedeanRing` to the supplied topology using
`Valuation.toTopologicalSpace_eq`. Mathlib's
`NonarchimedeanAddGroup.instTotallySeparated` then gives total separatedness,
hence total disconnectedness. The relevant import is
`Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`. This local
transport preserves the supplied topology and adds no global instance.

`padicPairGammaFactor` unpacks the conjunction, supplies the published
`residueCardinality_gt_one` and `unipotentQuotientHaar_isCompatible`, and calls
`gammaFactorOfAnalyticInput`. Its result has property
`IsPadicPairGammaFactor F psi nu pi sigma`. In particular, the final relation
quantifies over all compatible quotient measures, not just the measure used
for the analytic input. This universal property comes from the exact normalized
measure comparison already proved by the imported constructors. No external
quotient-measure existence or compatibility witness is required here.

`PadicSymmetricGammaInput` chooses `PadicPairGammaInput F psi nu pi sigma`
when `n ≤ r` and `PadicPairGammaInput F psi nu sigma pi` otherwise.
`padicSymmetricGammaFactor` applies the corresponding constructor and the
published rank-branch lemma. It returns a unit together with
`IsPadicSymmetricGammaFactor`. In the reversed branch the larger-rank
representation has the standard-character functional and the smaller one the
inverse-standard-character functional. In equal rank the original order is
preserved. Existing uniqueness of the relation applies to the result; no new
choice of factor relation is introduced.

## Scope

These are conditional constructions. The module does not establish the
analytic input, epsilon existence, self-dual measure existence, or original
and dual Whittaker type. It does not identify inverse-transpose pullbacks with
smooth contragredients, prove change-of-character or twist laws, descend to
representation classes, or construct nongeneric factors. Those remain separate
obligations. Rank ordering is implemented by the published convention and does
not claim a new rank-exchange theorem. There are no proof holes or new axioms.
