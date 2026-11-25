# The p-adic essential-vector level with trivial L-polynomials

`Langlands.Conductor.PadicTrivialLEssentialVectorLevelStatement.{uF,uV}`
concerns generic representations `π` of `GL_(n+2)(F)` for every `n : ℕ`,
including rank two. The field `F : PadicField.{uF} p` and the representation
space `V : Type uV` have independent universes. For every nonzero Whittaker
functional `ℓ` and every essential vector `w` of its coefficient model, the
conclusion is `w ∈ levelFixedVectors (modelRepresentation π ℓ) m`, where
the epsilon factor has the form `c q^(-ms)` for `m : ℕ`.

## Source correspondence

The first clause of Theorem (5.1)(ii) of Jacquet, Piatetski-Shapiro and
Shalika (1981), printed p. 211, asserts that the essential vector is
`K_r(m)`-invariant when `ε_π(X, ψ) = c X^m`. In (5.3), printed p. 213,
the authors compare its Whittaker dual with a translated essential vector
`W'` of the contragredient, then use the integral mirabolic invariance of
both vectors to obtain the level conclusion. The unit L-polynomial case
falls in the `deg P_π < r - 1` branch of (5.2) for every `r ≥ 2`.
[Conducteur des représentations du groupe linéaire](https://eudml.org/doc/163506)

Jacquet (2012), Remark 1, printed p. 523, observes that the 1981 existence
proof works when the standard L-factor is identically `1`. In (4.2),
printed pp. 209–210, the test supported on the integral cell produces
`∏ᵢ P_π(Xᵢ)` in the ideal of normalized integrals. With `P_π = 1` this
already supplies the unit needed for the essential identity. Applying
this argument to each representation when its standard factor is `1`
supplies both `W` and `W'` for (5.3). The two unit L-factor hypotheses
select that case of the 1981 argument. The Lean conclusion applies to
the supplied `w` in the original Whittaker model.
[A correction to Conducteur des représentations du groupe linéaire](https://msp.org/pjm/2012/260-2/pjm-v260-n2-p09-s.pdf)

## Pair factors and the dual model

The sources use Godement–Jacquet standard L- and epsilon factors. The Lean
formulation uses the JPSS Rankin–Selberg pair factors against the trivial character of
`GL_1(F)`. Reading the source argument in this formulation takes the
correspondence between these factor conventions. The two
`IsPadicSymmetricLPolynomial` premises specify the polynomial `1`, and
`IsPadicSymmetricEpsilonFactor` specifies the pair `(c, (m : ℤ))`.
[General essential-vector statement](EssentialStatement.md)

The dual hypothesis follows `SymmetricGammaExpressionStatement`. It uses
`inverseTransposePullback π`, `ψ.scale (-1)` for the inverse additive
character, the same additive Haar measure `ν.val`, and the inverse-transpose
pullback of the trivial rank-one representation. Pullback preserves
triviality. The `dualFunction` and `dualFunctional` constructions tie the
transformed Whittaker coefficient directly to this pullback on the
representation space of `π`. This gives a dual model using the pair-factor
convention without a smooth contragredient identification.

## Relation to the general level statement

`EssentialVectorLevelStatement` has the same essentiality and level
conclusion over arbitrary nonarchimedean local fields. Here the topology,
valuative relation and local-field structure come from
`F.canonicalTopologicalData`. The measure `ν :
LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ` packages
the additive Haar measure and the self-duality premise. The two unit
L-polynomial premises are additional hypotheses.

The p-adic relations insert the canonical residue cardinality and normalized
absolute value. The variables `q`, `abv`, `ϖ` and `μ` remain explicit in
`h : IsJacquetNormalization q ψ abv ϖ μ`, which controls the essential
identity. The residue-cardinality, uniformizer and unit fields of `h`
identify its `q` and `abv` with the canonical values. The latter equality
is available as `Conductor.SupercuspidalPadic.eq_normalizedAbsoluteValue`.

The factor relations supply Borel measurable structures for the field,
`GL_1(F)`, its upper unipotent subgroup and its unipotent quotient. This
removes explicit field and rank-one unipotent measurable and Borel
parameters. The measurable parameters used by `h` and the essential
identity are retained. Hausdorffness and total disconnectedness follow
from the canonical p-adic data.

Mathematically the general level proposition implies this one by
instantiation at `F.Carrier` with the canonical structures and `ν.val`
with `ν.property`. In these ranks the symmetric epsilon relation selects
the larger-rank-first branch, which gives `IsPairEpsilonFactor` with
canonical `q` and `abv`. Use the equalities from `h` to match its
normalization. Use the `GL_1` Borel instance and `h.borel_rankOne` to
identify the measurable structures of its rank-one integral with
the ones in the p-adic factor. The general proposition then gives
the stated membership of `w` independently of the two L-polynomial
certificates.

## Library inputs for a proof

The zero-cell lift `HighlyRamified.exists_zeroCellLift` is available for
every nonzero Whittaker functional of a generic representation in ranks
at least two. The Library also has `Conductor.isGeneric_inverseTransposePullback`,
`Conductor.scaledDualFunctional_ne_zero` and `IsJacquetNormalization.scaleNegOne`
for constructing the corresponding dual coefficient model and normalization.
The proof needs an essential vector there. It can combine the dual
L-polynomial certificate with
`HighlyRamified.isCharacterLPolynomial_of_isPadicSymmetricLPolynomial`
after identifying the pullback of the trivial character with the trivial
character. The zero-cell integrand comparison and its integral-one formula
in `HighlyRamified.EssentialInput` give the essential identity after
transport to the supplied compatible Borel measure. The zero-cell
restriction gives the integral invariance required for essentiality.

`Whittaker.mirabolicRestrictionInjectivity` and
`Conductor.essentialIntegralLastRowSupport` are published, as are the
resulting integral mirabolic invariance lemmas
`IsEssentialVector.mem_jacquetFixedVectors` and
`IsEssentialVector.right_jacquet_invariant`. With both essential vectors
and the epsilon premise transported to the normalization of `h`,
`Conductor.essentialDualComparison` supplies the comparison of (5.3).
`Conductor.mem_levelFixedVectors_of_rankInclusion_dual_comparison` then gives
level invariance from that comparison and the two integral mirabolic
invariances. These are the steps of the published conditional reduction
`Conductor.essentialVectorLevelStatement_of`, which takes a general
essential-vector existence theorem as an input. Here the required existence
step is the zero-cell construction for the dual under its unit L-polynomial
hypothesis and the supplied normalization.
