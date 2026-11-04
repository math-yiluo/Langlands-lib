# Complex exponential parameters on the actual rational valuation image

This construction implements the additive-parameter route in Renard 2026
V.3.20 on the existing actual image of rational-character valuations. It works
with general connected reductive groups over any nonarchimedean local field
supported by the shared framework. It does not replace that image by the
cocharacters of a split torus.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are V.2.3–V.2.6, printed pp.105–108/PDF pp.111–114,
for the actual norm kernel and valuation image, and V.3.19–V.3.20, printed
pp.115–116/PDF pp.121–122, for additive functionals, the exponential map,
basis-value lifts and periods. The implementation and choice of a principal
logarithm on basis values are internal constructions of that route.

## Actual objects and conventions

Write `Lambda = Additive (rationalDiscreteValuationImage G)`. This is the
additive copy of the range of `rationalCharacterValuation G`, not an assumed
lattice. Its projection is `rationalValuationImageProjection G`; its kernel
is the published actual `rationalCommonNormKernel G`.

`rationalImageComplexFunctionals G` is `Lambda →+ ℂ`.
`rationalImageParameterRealPart` takes the ordinary real part pointwise;
`rationalImageParameterOfReal` includes real functionals in this complex
space. Neither construction asserts an identification with the algebraic
character tensor space.

Put `q = LocalField.residueCardinality F` and `L = log q > 0`.
`rationalImageComplexCharacter G lambda` is the continuous character of the
actual discrete image with value
`exp (-lambda(a) * L)` at `a`. The zero and addition laws bundle it as
`rationalImageComplexExponential`, whose domain uses `Multiplicative` to
express the additive parameter group as a multiplicative group. Discreteness
supplies continuity of each character. No topology on the parameter space
or continuity in the parameter is asserted here.

The intrinsic value, norm and real-part laws show:

- the value is precisely the stated complex exponential;
- adding parameters multiplies characters;
- real parameters recover the existing `rationalImagePositiveCharacter`;
- the norm is `exp (-Re(lambda(a)) * L)`;
- `rationalImageRealPart` of the character equals
  `rationalImageParameterRealPart` of its parameter.

This uses the normalized `q^(-s)` convention throughout. The raw logarithmic
modulus equals `-L` times this real parameter; the later raw-log formula in
V.3.20 does not identify those two conventions.

## Period subgroup and chosen lift

`rationalImageComplexPeriod` is `2*pi*i/L`, with the positive sign used in
the source. `rationalImagePeriodEmbedding` multiplies each integer-valued
additive functional on the same actual image by that scalar.
`rationalImagePeriodLattice` is its additive range. Its name specifies the
intended period subgroup; this file does not prove the exponential-kernel
identification, discreteness or cocompactness.

`rationalImageComplexLift G hG chi` uses
`rationalReductiveValuationBasis G hG`, the existing finite integer basis
of the actual image. The published rational-character lattice theorem
discharges finiteness from `IsConnectedReductive G`; no new finite-rank
hypothesis is imposed on the group. On basis vector `b_i`, the lift is
`-Complex.log (chi(b_i))/L`. The basis constructor extends these values
additively. This is a set-theoretic chosen lift, with no asserted
additivity or continuity in `chi`.

The reconstruction law `rationalImageComplexCharacter_lift` follows by
the injectivity of the existing finite character coordinates. On each
basis vector the scale cancels because `L` is nonzero, and
`Complex.exp_log` recovers the nonzero character value. This intrinsic law
certifies that the constructed lift has the required value.

## Canonical rational points and remaining comparisons

For an affine group scheme locally of finite type,
`rationalCanonicalUnramifiedComplexExponential` composes the same
exponential with the published canonical image-to-unramified-character
equivalence. The point group carries `rationalPointTopology F G.X`.
Its value at every actual point `g` is
`exp (-lambda(H_G(g)) * L)` with the existing image projection. Connected
reductivity supplies the affine and finite-type assumptions when this
adapter is used in that setting.

The exact kernel formula, equivalence of lifts modulo the period subgroup,
independence of the real part of a lift and the full imaginary-parameter
description remain separate statement and proof obligations. Also retained
are the comparisons with `X*(G) ⊗ ℂ` and the split-center tensor spaces, the
pure-tensor formula using algebraic character norms, parameter topologies,
the complex algebraic torus structure and the compact imaginary quotient.
This unit alone does not establish the full V.3.20 identification.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
