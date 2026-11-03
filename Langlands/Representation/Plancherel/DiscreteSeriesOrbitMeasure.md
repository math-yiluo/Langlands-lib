# Locally preserved measure on an actual discrete-series twist orbit

This derived construction equips the existing canonical discrete-series
twist orbit with a measure relative to a supplied invariant character
measure. It implements the orbit convention in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)* (2003), VI.3, printed p.302 (PDF p.68): the map sending a
unitary unramified character to the twisted class locally preserves
measures. The orbit-stabilizer parameterization comes from III.7, printed
p.273 (PDF p.39). The quotient pushforward formula, its construction laws
and the base-point comparison below are internal derivations.

The character measure is fixed earlier in I.1, printed p.239 (PDF p.5).
There the split-center character group has Haar mass one and restriction
from the group's character group locally preserves measures. This pair
retains the scale of its supplied character measure. It does not
construct that original restriction normalization.

## Existing objects and Borel measurable spaces

The parameters are a general nonarchimedean topological group `G`, a
normal subgroup `A` with a proof `hA` of centrality, a measurable space
on `G / A`, a Haar measure `mu` on that quotient, and a family `nu` of
positive multiplicative characters. `DiscreteSeriesClass A hA mu` is the
existing square-integrable subtype of the canonical irreducible
admissible smooth representation classes. The representation carrier
universe is independent of the group universe. To identify this generic
quotient convention with the source, `A` must be specialized to the
actual split component and `nu` to the required norm-character family.
No new representation framework is introduced here.

`unitaryUnramifiedCharactersMeasurableSpace` gives the existing unitary
character group the Borel measurable space of its compact-open topology;
the accompanying Borel-space instance records that choice.
`discreteSeriesOrbitMeasurableSpace` and its Borel-space instance use the
Borel sets of the existing orbit topology from
`DiscreteSeriesOrbitTopology`. That topology is transported through the
actual orbit-stabilizer equivalence. No topology or measurable space on
the entire smooth dual is required.

## Measure and construction laws

Fix a base class `omega`, its actual unitary stabilizer
`S = discreteSeriesStabilizer A hA mu nu omega`, a proof that `S` is
finite, and a measure `lambda` on the unitary character group. With
`p = discreteSeriesOrbitMap A hA mu nu omega`, define

\[
  \operatorname{discreteSeriesOrbitMeasure}(\omega,\lambda)
    = |S|^{-1}\,p_*\lambda.
\]

The map `p` sends a character to its actual twist of `omega`, as proved
in the existing orbit-topology module.
`discreteSeriesOrbitMeasure_apply` evaluates measurable orbit sets by
this inverse-image formula. `discreteSeriesOrbitMeasure_univ` gives total
mass `|S|⁻¹ * lambda univ`, and `discreteSeriesOrbitMeasure_smul` proves
compatibility with every extended nonnegative scalar. These laws do not
need invariance of `lambda`.

`discreteSeriesOrbitMeasure_eq_map_quotient` identifies the measure with
the pushforward of `finiteCharacterQuotientMeasure S lambda` through
`discreteSeriesOrbitHomeomorph`. Its statement allows any Borel
measurable space on the character quotient. The proof uses the
pushforward composition and scaling laws and the defining factorization
of `p`.

`lintegral_discreteSeriesOrbitMeasure` proves, for every measurable
extended nonnegative function `f` on the orbit,

\[
 \int_{\mathcal O} f(\eta)\,d\eta
  = |S|^{-1}\int_{\operatorname{Im}X} f(p(\chi))\,d\lambda(\chi).
\]

This is the nonnegative integral formula and allows infinite values. It
does not assert convergence of complex integrals or wave packets.

## Local preservation and base-point independence

The general construction law
`IsLocallyMeasurePreserving.homeomorph_comp` transports a locally
preserved measure through a homeomorphism of Borel target spaces.
It retains the source's open injectivity charts. Measurable images
follow from the homeomorphism's measurable embedding, and its inverse
cancels the image in the pushforward evaluation.

`isLocallyMeasurePreserving_discreteSeriesOrbitMap` assumes that
`lambda` is left invariant. In its proof the character quotient is
given its Borel measurable space. The finite-quotient theorem supplies
local preservation for the quotient projection: the character group
is Hausdorff, its finite subgroup is discrete, and counting its disjoint
translates on local charts cancels the factor `|S|⁻¹`. Composition with
the existing orbit homeomorphism and the quotient-measure comparison
prove local preservation for the actual twist map `p`. The
local-preservation conclusion is proved, not supplied as a premise.

`discreteSeriesStabilizer_unitaryTwist` proves that twisting the base
class by a unitary character leaves its stabilizer equal as a subgroup.
The proof commutes the two character actions and cancels the base twist.
`map_discreteSeriesOrbitMeasure_baseChange` states that the existing
identity-on-classes homeomorphism
`discreteSeriesOrbitBaseChange omega chi` pushes the measure at
`chi • omega` to the measure at `omega`. The theorem explicitly binds
finiteness at both base points; the preceding equality makes those two
finiteness conditions equivalent. It uses the same invariant `lambda`
on both sides.

For that comparison, composing the new-base orbit map with the
base-change map is the original orbit map precomposed with character
translation. Left invariance cancels this translation in the
pushforward, and equality of stabilizers identifies the cardinality
factors. Thus the measure is independent of the chosen base class
through precisely the existing identity-on-classes comparison.

## Remaining realization and analytic obligations

Finiteness of the actual stabilizer remains an explicit premise, rather
than an analytic or representation-theoretic structural assumption.
Applying this construction to rational points with all rational norm
characters requires the existing conditional stabilizer-finiteness
result and its displayed actual-image finite-index premise, or a
verified proof discharging that premise. The current pair does not
construct the actual split-component inclusion, prove finite index,
realize the I.1 character scale, or compare image rank with split-center
dimension. The character measure is arbitrary unless left invariance
is explicitly assumed for the local and base-change results.

This is a measure construction on individual existing twist orbits.
Smooth coefficient families, complex integral convergence, formal
degrees, the density, wave packets, spectral finiteness and the
Plancherel theorem remain separate obligations.
