# Scalar tests and conditional rationality of actual compact standard operators

This derived supporting module connects the actual compact-picture standard
integral with the conditional vector and operator cancellation results. It
proves four things:

- point evaluations against smooth functionals separate compact sections;
- given explicit local integrable bounds, the actual operator is continuous
  under these tests;
- the actual character spaces are first countable;
- on the literal Levi point subgroup, the compact rationality predicate
  `StandardCompactRationalOn` follows from these inputs, local hypersurface
  divisibility, and one common nonzero regular numerator.

It proves neither the domination bound nor the numerator identity nor local
divisibility. It adds no premise to
`ConditionalParabolicIntertwiningStatement`.

## Compact scalar tests

The setting is a locally compact nonarchimedean group `G`, a semidirect
decomposition `h` of `P` as `M` times `U`, an open subgroup `K`, and a
complex smooth representation `A` of `M`. Each test index is a pair
`(k, ℓ)`, where `k` is a point of `K` and `ℓ` is an element of
`SmoothDual A.representation`.

`compactPictureScalarTests h K A (k, ℓ)` is the complex linear functional on
`CompactInductionPicture h K A` that evaluates a section at `k` and then
applies `ℓ`. Additivity and homogeneity come from those of `ℓ`. The
compact-picture carrier needs no topology.

`compactPictureScalarTests_separates` assumes `M` is closed in `G`. If two
compact sections agree under every test, they are equal. For each `k`, the two
values in the representation space of `A` agree under every smooth functional.
They are then equal by the existing injectivity into the smooth bidual,
`smoothBidual_injective_of_compact_cofinal`, applied to the compact-cofinality
proof `compactCofinal hM` for the closed subgroup `M`. Equality at every point
of `K` gives equality of the subtype-valued sections.

## Weak continuity from local domination

`CompactIntegralLocallyDominatedOn ... Ω` is a Prop-valued hypothesis about a
parameter subset `Ω` of `unramifiedCharacters ν`. It says the following. Take
any fixed compact section `f`, compact point `k`, original smooth functional
`ℓ`, and parameter `χ₀` in `Ω`. Then some real function `bound` on the
quotient `QuotientSpace (U := U) U'` is integrable for the supplied measure
`qν`. Moreover, for all parameters of `Ω` near `χ₀`, the norm of `ℓ` applied to
the actual integrand `unramifiedCompactIntegrand` is bounded by `bound` almost
everywhere. This is the hypothesis Waldspurger's dominated-convergence argument
uses. It is assumed here, not proved.

`standardCompactOperator_isWeaklyContinuousOn_of_dominated` assumes:

- first countability of the character space;
- for every parameter in `Ω`, full source domain of the actual standard
  integral for the twisted representation;
- the domination hypothesis on `Ω`.

It proves that, for each fixed compact section `f`, the family
`χ ↦ standardCompactOperator ... χ A (hfull χ) f` on the subtype `Ω` is
continuous under every target test `compactPictureScalarTests h' K A`. At
each `χ₀`, the proof feeds the chosen bound to the published
`continuousAt_standardCompactOperator_scalar_of_dominated` along the subtype
inclusion. All structural data enter as explicit hypotheses: the
unimodular-modulus and squared-modulus compatibilities, the measures and the
quotient-integration compatibility.

## First countability of actual character spaces

Section `ActualTopology` has a nonarchimedean local field `F`, a group scheme
`H` over `F`, a supplied topology on its rational points, continuity `hp` of
`rationalValuationImageProjection H`, and connected reductivity `hH`.

`firstCountableTopology_rationalUnramifiedCharacters` proves that the character
space of the full family `rationalNormCharacters H` is first countable. The
existing homeomorphism
`(rationalImageUnramifiedContinuousEquiv H hp).symm.trans
(rationalReductiveImageCharacterCoordinates H hH)` embeds it into a finite
product of copies of `ℂˣ`. `ℂˣ` is first countable via its embedding into `ℂ`,
and first countability passes along embeddings.

Next, take a topological group isomorphism
`e : rationalPoints H ≃ₜ* L`.
`firstCountableTopology_transportedRationalUnramifiedCharacters` proves first
countability for the transported family `ψ ↦ (rationalNormCharacters H ψ).toMul ∘ e⁻¹`.
The proof uses the existing homeomorphism `unramifiedCharactersHomeomorph e`.

## Transported conditional cancellation

`transported_isRationalOperatorOn_of_weak_continuity` explicitly assumes
`hdiv : RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u}`.
Its other hypotheses are:

- an arbitrary open subset `Ω` of the transported character space;
- complex linear scalar tests that separate points of the target `W`;
- a nonzero regular function `b` for the transported family;
- an operator family `T : Ω → V →ₗ[ℂ] W`, weakly continuous under those tests
  for each fixed source vector;
- `IsPolynomialOperatorOn Ω (b • T)`.

The conclusion is `IsRationalOperatorOn Ω T`. The proof pulls everything back
to the actual rational points of `H`:

- the existing transport law `isRationalOperatorOn_transport_iff` turns the
  goal into rationality on the preimage of `Ω` under
  `unramifiedCharactersHomeomorph e`, which is open;
- the regular function becomes `(unramifiedRegularFunctionsEquiv e ν).symm b`,
  which is nonzero because the algebra equivalence is injective;
- weak continuity composes with the continuous homeomorphism;
- polynomiality transports by `isPolynomialOperatorOn_transport_iff`.

Then `rationalUnramified_isRationalOperatorOn_of_weak_continuity`, from the
bundled vector cancellation module, gives rationality. It chooses one denominator before every source vector,
nonzero at every point of the region. The universes of `V`, `W` and the test
index stay independent.

## Literal Levi specialization

Section `LiteralLevi` uses the variables of the canonical region module:

- a parabolic root presentation `r : ParabolicRootPresentation p l a`;
- `[IsAffineHom G.X.hom]`, `[IsAffine M.X.left]` and
  `[LocallyOfFiniteType M.X.hom]`;
- the canonical rational-point topologies on `G` and `M`, as local instances.

The literal norm family `parabolicLeviRationalNormCharacters r` is by
definition the transported family for `e = parabolicLeviPointHomeomorph r`.
Its continuity premise is the published
`continuous_rationalValuationImageProjection M`, and its reductivity premise
is `r.isCompatible.levi.isConnectedReductive`. No extra premise is needed.

`firstCountableTopology_parabolicLeviUnramifiedCharacters` and
`parabolicLevi_isRationalOperatorOn_of_weak_continuity` are the transported
results specialized to this family. The cancellation still assumes `hdiv`
explicitly.

`parabolicLevi_standardCompactRationalOn_of_dominated` concerns actual point
subgroups `Ppt`, `Upt`, `P'pt` and `U'pt` of the rational points of `G`. It
takes the following data:

- two semidirect decompositions with the literal Levi point subgroup
  `parabolicLeviPointSubgroup p l`;
- closedness, unimodular modulus, compact Iwasawa factorizations and projection
  continuity;
- the measures, quotient-integration compatibility and squared-modulus
  compatibility, as in the target statement;
- local compactness, the nonarchimedean group property and the Hausdorff
  property of the ambient point group, as instance binders.

For any complex smooth representation `π` of the literal Levi point subgroup,
the theorem assumes:

- an open parameter subset `Ω`;
- full source domain at every parameter of `Ω`;
- `CompactIntegralLocallyDominatedOn` on `Ω`;
- one nonzero regular function `b` for which `b` times the actual
  `standardCompactOperator` family is `IsPolynomialOperatorOn Ω`.

From these and `hdiv`, it proves
`StandardCompactRationalOn h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
qν μU' μI hqν hM hsq Ω π hfull`, where:

- `ν` is `parabolicLeviRationalNormCharacters r`;
- `hν` is `continuous_parabolicLeviRationalNormCharacters r`;
- `hM` is `isClosed_parabolicLeviPointSubgroup r`.

These are exactly the terms the target statement uses. The proof takes the
target compact scalar tests, uses their separation for the closed literal
Levi, gets weak continuity from the domination theorem, and applies the
literal conditional cancellation. Admissibility and finite length of `π` are
not needed for this implication.

## Provenance and remaining obligations

The module is derived. It combines the published compact-continuity, transport
and conditional cancellation interfaces with smooth-bidual injectivity and
standard first-countability facts. Its rationality conclusion uses the
convention of Waldspurger, *La formule de Plancherel pour les groupes p-adiques
d'après Harish-Chandra* (2003), IV.1 (printed p. 277): one denominator is
chosen before the input vector. No literature theorem is used in place of an
omitted step.

Several obligations remain separate:

- the local hypersurface divisibility premise `hdiv`;
- the actual local integrable domination bound;
- full convergence on the saturated orbit region;
- one common nonzero regular numerator for the whole standard operator;
- openness of the region;
- the host theorem `ConditionalParabolicIntertwiningStatement`.

This module proves none of them.
