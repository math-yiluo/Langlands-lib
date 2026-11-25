# Actual Plancherel wave packets for a standard Levi

Lean module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacket`,
namespace `Langlands.HarishChandraSchwartz`.

## Source and provenance

This is a derived specialization of existing Library constructions. The source
is J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`,
PDF SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
VI.3, printed pp.301–302 / PDF pp.67–68, defines the packet by integrating
`mu(omega) E_P^G(q_omega)(g)` over the unitary discrete-series orbit.
The source's I.1 scale (printed p.239 / PDF p.5) and the VI.3 orbit measure
are implemented by the imported `StandardLeviCharacterMeasure` adapter.

The module names the existing integral after substituting the existing
`standardLeviPlancherelWeight`. It also proves the parabolic identification
needed to use the dynamic scalar with this standard-parabolic coefficient.
It introduces no new density, orbit, section space or Schwartz topology.

## Data and retained premises

The field `F` is an arbitrary nonarchimedean local field in universe `u`.
The representation-carrier universe `uV` is independent. The connected
reductive group scheme `G` is affine and locally of finite type over `F`.
A maximal split torus `i`, generic cocharacter `nu`, simple-root index `I`
and standard cocharacter `zeta` specify the actual standard parabolic and
literal standard Levi subgroup of `G(F)`, with their canonical topologies.
No assumption on the characteristic or on splitness of `G` is made.

The inducing `pi` is a canonical complex irreducible admissible `SmoothRep`
of that literal Levi. Its square-integrability hypothesis is modulo the
explicit normal central subgroup `C`, with quotient Haar measure `mu` on
`M_I(F)/C`. The unitary orbit is the existing
`discreteSeriesOrbit` of `discreteSeriesClass C hC mu pi hsq` for
`leviRationalNormCharacters i nu I`. The stabilizer is assumed finite in
this general wrapper. A character measure `rhoX` is an explicit argument;
the source-normalized targets specialize it to the I.1 adapter.

All premises of `standardLeviPlancherelWeight` remain explicit: relative-root
reflection and central-split-torus character statements, compact open `Ks`
with both parabolic factorizations, forward and reverse continuation data,
nonempty open convergence loci contained in the full domains, a nonempty
open generic irreducibility locus, and full-unitary regularity `hreg` of
the inverse conditional composition scalar. These are retained obligations,
not consequences of square integrability proved here. The packet's compact
open `K`, its compactness `hKc`, and minimal-parabolic Iwasawa pair `hPK`
are independent of `Ks`.

## Declarations and implemented proofs

`standardLeviPlancherelParabolic_eq` proves
`parabolic (zeta composed with i) = standardParabolicPoints i nu (rootSet i nu I)`.
Its proof evaluates the already published `standardCocharacter` subgroup-functor
equality at the rational-point test object, then takes symmetry. Thus this
identification is discharged rather than imposed as an additional premise.
The inducing representation remains on the literal standard Levi; the
imported weight internally pulls it back through its canonical dynamic-Levi
homeomorphism.

`standardLeviPlancherelWavePacket` is exactly
`rationalInducedOrbitWavePacket` with the imported actual weight, rather than
a freely chosen smooth function. For every existing smooth orbit section `q`
and `g` in `G(F)`, `standardLeviPlancherelWavePacket_apply` proves by reflexivity
that its value is

```text
integral over omega in O of
  standardLeviPlancherelWeight(omega) *
  rationalInducedOrbitCoefficientMap(q)(omega)(g)
with respect to discreteSeriesOrbitMeasure(..., rhoX).
```

Here the quotient orbit measure is the reciprocal stabilizer cardinality
times the character measure's pushforward. The imported adapter identifies
this exact measure with the I.1/VI.3 source normalization when `rhoX` is its
standard-Levi character Haar. That normalization generally has total mass
`|ker restriction to the split component| / |self-twist stabilizer|` on the
orbit. The actual valuation-image finite-index premise remains in that
adapter and in the principal targets.

## Scope

This module supplies a definition and the two comparison formulas. It proves
no integrability or full Schwartz estimate for the packet, and no continuity
of synthesis. Those are separate Prop-valued targets. The previously proved
central-valuation decay for the actual weight controls only central lattice
coordinates; the Schwartz space uses all real seminorms for the full matrix
height, so that decay does not settle Proposition VI.3.1 (printed pp.302–305).
The existing section topology is reused; its comparison with Waldspurger's
finite-dimensional tensor-product topology remains a separate obligation.
