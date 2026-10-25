# Relative Hom comparison for an arbitrary outer quotient

Author: Worker 435. The quantified telescope is copied from Worker 19's
published `GLRelativeCosocleMultiplicityStatement`. This pair defines an
internal proposition; it does not prove a comparison.

`Langlands.GLRelativeCosocleHomComparisonStatement` retains that statement's
entire telescope and every hypothesis through the actual outer-quotient
surjection. The independent universes are `uF` for the field, `uV` for the
fine carrier, `uM` for the middle carrier, `uW` for the coarse carrier and
`uZ` for the outer quotient carrier.

For every prime and compatible topological realization of an actual finite
p-adic extension, the ambient rank is positive. The nested block shapes are
`B`, `D = B.flatten Q` and `D.flatten R`. The direct refinement `S` and actual
equality `h : D.flatten R = B.flatten S` identify the same fine Levi. The
fine representation `ω` is irreducible, Levi cuspidal and unitarizable.
The parameter `v₀` satisfies `IsPositiveRootParameter D R v₀`, using the
existing adjacent scalar roots in reciprocal block-size determinant
coordinates. The equality `h` transports `ω` and `v₀` to `ωB` and `vB`.

The independent middle representation `σ` is irreducible and
`IsLeviSquareIntegrable T D σ`, and receives an actual surjective intertwiner
from `innerInduced T D R (fineTwist T D R ω v₀ 0)`. The coarse representation
`π` is an arbitrary irreducible `IsLeviTempered T B π` representation.
For every strictly decreasing coarse vector `t`, put
`πt = Rep.of (T.leviRealPowerTwist B t π.ρ)`. The independent ambient
representation `J` is irreducible and receives an actual surjective
intertwiner from `CuspidalJacquetMultiplicity.induced T B πt`.

Write `τ₀ = fineTwist T B S ωB vB 0` and
`τt = fineTwist T B S ωB vB t`. The conclusion concerns the actual complex
linear intertwiner spaces

- `Hout = τt.ρ.IntertwiningMap (T.normalizedComposedOppositeJacquet B S J.ρ)`;
- `Hin = τ₀.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)`.

Both are Hom spaces for the same actual refined subgroup
`Geometric.refinedLevi F.Carrier B S`. The first target is the genuine
composed opposite coinvariant quotient of `J` itself, with carrier in `uZ`.
The second is the genuine refined opposite coinvariant quotient of `π`,
with carrier in `uW`. Each source retains the fine carrier in `uV`.
The conclusion asserts finite dimensionality of each Hom space and equality
of their complex finranks. Either space and the common dimension may be
zero. Finite dimensionality is explicit because finrank alone does not
exclude an infinite-dimensional space.

All twists and inductions are the existing actual constructions. The fine
determinant exponents are `-vB` at zero and `-vB` plus the restricted coarse
vector at `t`, with residue-normalized absolute value `q^(-valuation)`.
Upper normalized induction uses right translation and positive-half-modulus
covariance. The opposite quotients use the inverse half of the opposite
full modulus, which is the positive half of the corresponding upper full
modulus. No normalization character is supplied as data.

There is no fine or middle support premise on `π`, no premise that `J` is
a quotient of the fine ambient induction, and no finite-dimensionality
premise on representation carriers or Hom spaces. The statement supplies
no chosen Hom equivalence, parameter family, occurrence-continuation
theorem, canonical quotient representative or cosocle construction.
The existing cosocle multiplicity conclusion is neither asserted nor used
as a premise here.

The provenance is internal. Silberger, *The Langlands quotient theorem for
p-adic groups* (1978), fixes the nested data on printed p.99 and proves
Proposition 5.9 on p.102 using two reciprocity formulas. The first formula
uses the opposite Jacquet module of the irreducible quotient, not of the
whole outer induction. Its last line refers to the continuation argument
in the proof of Lemma 5.6 on p.101. These passages motivate this
Hom-dimension interface; they do not literally state its Lean telescope
or the two explicit finite-dimensionality conclusions.

A later proof must establish actual second-adjointness applicability,
quotient extraction and the multiplicity-sensitive continuation and
tempered-exponent argument for the arbitrary coarse input. A raw
Jordan–Hölder count in a possibly nonsemisimple cuspidal isotypic Jacquet
block does not by itself compute a Hom dimension. The fixed-central-exponent
projectivity invoked on p.100 cannot silently be extended to central
self-extensions, and admissibility does not imply full Jacquet
semisimplicity. The unrestricted wording of Lemma 5.3 has a documented
[scope obstruction](../../../notes/jacquet/silberger-lemma53-scope.md).
A constituent-restricted generic comparison requires its support
hypotheses; those hypotheses are not supplied for arbitrary `π` by this
statement. Proving the proposed interface must not use the consuming
cosocle theorem or downstream full classification.

The retained original is registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
PDF SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The full article was read during the parent proof investigation; pp.99–102
and the displayed p.102 formulas were revisited for this pair.
