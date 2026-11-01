# Scalar-normalized rational chart comparison

Worker 101, using Worker 146's rational normalization and ring-map uniqueness
helpers. This is internal derived infrastructure for scalar rational descent.

Let `A` be a presented positive-polyradius affinoid algebra over an ultrametric
normed field `K`, let `ι : K →+* L` be isometric, and suppose `c` and `τ` realize
the base radii and the relative radii of a rational chart `d`. The universes
of `K` and `L` are independent. Write `Q` for the published strict scalar
extension of `A`. The definition `strictBaseChangeBoundedHom` packages its
contractive scalar-change map, and `d.scalarNormalizedStrict` abbreviates
the actual strict rational data with denominator `ι(g)` and numerators
`τ_j⁻¹ ι(f_j)` in `Q`.

The raw strict algebra `d.rawStrictScalarExtension` is the strict scalar
extension of the original weighted rational quotient `d.algebra`, using
the combined realizing tuple `Fin.addCases c τ`. The map
`d.rawStrictBaseMap : Q → S` is the actual strict variable-adjunction map
from `StrictBaseChangeAdjoin`. Its scalar-change square is
`rawStrictBaseMap_scalar`. The new strict coordinates in `S` are named
`d.rawStrictFraction`.

The series identity `GeneralizedTateAlgebra.baseChange_X` is proved
coefficientwise. Descending it through the genuine presentation map gives
`strictBaseChangeHom_coordinate` and `scalar_fraction`: the image of an
original fraction coordinate is `τ_j` times its raw strict coordinate.
The raw strict coordinates have bounded monomials, since they are a subtuple
of the images of the strict Tate variables. Applying scalar change to the
original fraction equations, then multiplying by `τ_j⁻¹`, proves
`rawStrictFraction_equation`. Positivity of the relative radii implies
`τ_j ≠ 0`.

When `L` is complete, `d.scalarComparison` is the bounded `L`-algebra map
from the normalized strict rational quotient to `S` obtained by the
published `RationalLocalization.liftFromBase`. The preceding bounded
monomials and equations are its actual inputs. The identities
`scalarComparison_baseMap` and `scalarComparison_fraction` are the
corresponding evaluation formulas.

For any bounded forward ring map `F` from `d.algebra` to the normalized
strict quotient satisfying the displayed base square,
`scalarComparison_comp_map` proves that the composite with this comparison
is the original scalar-change map on `d.algebra`. The proof applies
`ringHom_ext_over_base` to the common contractive map from `A` to `S`.
The common map is contractive by the published bounds for the original
rational base map and scalar change.

Given a bounded additive coefficient map `π : L →+ K` satisfying
`π(ι(a)x) = a π(x)`, the definition `d.scalarRetraction` composes the
comparison with the published coefficient retraction from `S` to
`d.algebra`. The theorem `scalarRetraction_baseMap` is its commuting square
with the retraction from `Q` to `A`; it follows directly from the
variable-adjunction retraction square. If additionally `π(1) = 1`,
`scalarRetraction_map` proves that this additive map is a left inverse
to any such `F`, using the composite identity and the original
coefficient left inverse. The norm estimate `norm_scalarRetraction_le`
is `‖R(b)‖ ≤ D ‖scalarComparison(b)‖`; boundedness of the comparison
therefore also gives a linear norm bound for `R`.

The constructions impose no reducedness, proper-ideal, nonempty-spectrum,
positive-arity, or nontrivial-valuation assumptions. Completeness of `K`
is not required here. Completeness of `L` is used for strict rational
evaluation. This module constructs the comparison and additive retraction;
it does not construct the forward map or assert rational gluing.
