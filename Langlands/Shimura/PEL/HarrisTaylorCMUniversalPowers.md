# Relative powers of the universal CM abelian family

## Source

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p. 98 (one-based PDF p. 106), lets
\(\pi : A \to X_U\) be the universal abelian variety and
\(\pi_m : A^m \to X_U\) its \(m\)-fold self-product over \(X_U\). It
uses the endomorphisms \([2]_x\) of multiplication by 2 on the \(x\)-th
factor and the symmetric group acting on the factors to build the
idempotents applied to \(R(\pi_m)_*\). III.1, printed p. 91 (PDF p. 99),
states that \(X_U\) is smooth and projective over \(F\). The book is
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This module applies the general construction of
[relative powers](../../AbelianScheme/RelativePower.md) to the abelian
family `cmUniversalAbelianFamily` of
[HarrisTaylorCMUniversalClass](HarrisTaylorCMUniversalClass.md), on
each connected component of a represented level. It states nothing
about cohomology.

## Powers on the components

For a representation `rep : CMLevelRepresentation U` and a connected
component `c` of `rep.base`, `cmUniversalComponentPower rep c m` is
`relativePower (cmUniversalAbelianFamily rep c) m`, an object over the
component scheme; at `m = 0` it is the component itself.
`cmUniversalComponentPowerToLevel rep c m` is its structure map followed
by the actual open inclusion `componentι` of the component into the
level (`cmUniversalComponentPowerToLevel_eq`,
`cmUniversalComponentPowerToLevel_zero`). The powers on the components,
with these maps, are the componentwise assembly of \(\pi_m\) over the
whole level: the map from the power over `c` factors through the
component `c`, where it is the structure map of the power.

## Smoothness and properness

`componentι_isClosedImmersion` proves that the inclusion of a connected
component of a locally Noetherian scheme is a closed immersion: it is a
preimmersion whose range is the connected component of a point, which
is closed. Being also an open immersion, the inclusion is smooth and
proper. `cmUniversalComponentPower_hom_smooth_proper` is
`relativePower_smooth_proper` for the family over the component.
`cmUniversalComponentPower_smooth_proper` proves that the map to the
level and its composite with the structure map `rep.base.obj.hom` to
`Spec F` are smooth and proper. Smoothness over `F` uses the field
`rep.smooth` of the representing evidence; properness over `F` uses
`IsHProjective.isProper` applied to `rep.projective`.

## Multiplication by two and permutations

`cmUniversalComponentPowerDouble rep c m i` is the scheme map underlying
`relativePowerDouble`, multiplication by two on the factor `i`; it is
\([2]_i\). `cmUniversalComponentPowerPermute rep c m σ` is the scheme
map underlying `relativePowerPermute`, whose factor `j` is the original
factor `σ j`. Their formulas on projections are
`relativePowerDouble_projection` and `relativePowerPermute_projection`.
Both commute with the map to the level
(`cmUniversalComponentPowerDouble_toLevel`,
`cmUniversalComponentPowerPermute_toLevel`). The permutation maps
satisfy `cmUniversalComponentPowerPermute_one` and the composition law
`cmUniversalComponentPowerPermute_comp`: the map of `σ` followed by the
map of `τ` is the map of `σ * τ`.
`cmUniversalComponentPowerPermute_double` proves that the map of `σ`
followed by multiplication by two on the factor `i` equals
multiplication by two on the factor `σ i` followed by the map of `σ`.

## The scheme tower

For a proof `q` of `CMRepresentabilityStatement`,
`cmSchemeTowerComponentPower q U c m` is the power over the component
`c` of the level `U` of `cmSchemeTower q`, and
`cmSchemeTowerComponentPowerToLevel q U c m` is its map to
`(cmSchemeTower q).obj U`. `cmSchemeTowerComponentPower_smooth_proper`
proves that this map and its composite with the structure map of the
chosen representing scheme to `Spec F` are smooth and proper.
