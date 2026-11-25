# Actual source-normalized Plancherel wave-packet targets

Lean module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketSchwartz`,
namespace `Langlands.HarishChandraSchwartz`.

## Source and status

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered source
`waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The relevant original passages are I.1, printed p.239 / PDF p.5;
VI.3's topology and integral, printed pp.301–302 / PDF pp.67–68;
and Proposition VI.3.1 and its proof, printed pp.302–305 / PDF pp.68–71.

The three new declarations are definitions returning `Prop`. They state
membership, continuous linear synthesis, and their conjunction for the existing
actual objects. They are not proofs of those propositions. The formal targets
retain the conditional density's hypotheses and the actual valuation-image
finite-index premise. They use the existing section topology; comparison with
the source's tensor-product topology remains a separate proof obligation.
These differences from a completed unconditional formalization of VI.3.1 are
part of the statements' intended scope.

## Actual group, inducing representation, and retained premises

`F : Type u` is an arbitrary nonarchimedean local field, with no
characteristic-zero assumption. `G` is an affine, locally finite type,
connected reductive group scheme over `F`. A maximal split torus `i`, generic
cocharacter `ν`, standard index `I`, and standard cocharacter `ζ` are displayed.
The parabolic is the actual
`standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I)`.
Write `L` for its intrinsic `Standard.leviScheme` and `M` for the literal
`standardLeviPoints` subgroup of `rationalPoints G`. All use the canonical
rational-point and subgroup topologies. There is no split or quasisplit
restriction on `G`.

The inducing object
`π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M)`
uses the canonical complex `SmoothRep` interface. The field universe `u`
and representation-carrier universe `uV` are independent.
For an affine commutative group scheme `T`, the displayed
`s : T.toGrp ⟶ L` satisfies `hs : IsSplitComponent s`.
The central subgroup is fixed to

```text
CM = rationalLeviSplitCenter I s.
```

It is the image in `M` of `(rationalPoints.map s).range` under the canonical
intrinsic-to-literal Levi homeomorphism. The centrality proof is
`rationalLeviSplitCenter_le_center I s hs`.
The normality instances for `CM` and the intrinsic image are explicit Lean
parameters; both follow from their inclusion in the respective centers by
`Subgroup.normal_of_le_center`. They add no mathematical restriction.

`mu` is the displayed Borel Haar measure on the literal quotient `M / CM`.
The hypothesis `hsq` is precisely
`IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu`.
The imported `standardLeviCentralQuotientHomeomorph` identifies this quotient
with `L(F) / (rationalPoints.map s).range`;
`standardLeviIntrinsicQuotientHaar` pulls `mu` back along that equivalence,
and `map_standardLeviIntrinsicQuotientHaar` proves that its pushforward is
exactly `mu`. The main inducing representation remains on the literal `M`.

The actual-image premise

```text
hindex : (RenardCartan.splitValuationImage s).FiniteIndex
```

remains visible in every target. For a split component `s` it is proved by
`finiteIndex_splitValuationImage_of_isSplitComponent` (module `RationalOrbitCentralFiberAdapter`),
which these targets do not use.
Each component target installs the proved
`finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ`.
There is no extra assumed finite self-twist stabilizer.

The weight is exactly the imported `standardLeviPlancherelWeight`.
Its retained parameters include `RelativeRootReflectionExistenceStatement`,
`CentralSplitTorusCharacterStatement`, a compact open `Ks` with forward and
opposite parabolic factorizations, forward and reverse continuation data
for the canonical dynamic-Levi pullback of `π`, nonempty open convergence
loci lying in their full domains, generic irreducibility on a nonempty open
locus, and full-unitary regularity `hreg` of the inverse conditional
composition scalar. These remain conditional structural and analytic inputs;
the targets do not prove them.

The packet's compact open `K`, its compactness `hKc`, and minimal-parabolic
Iwasawa pair `hPK` are separate from `Ks`. The height uses the displayed
`ρ : MatrixRepresentation G (Fin N)`, with `Nonempty (Fin N)`. It is the
existing full matrix height `rationalHeight ρ`, the logarithm of the maximum
normalized absolute value of the entries of `ρ(g)` and its inverse.
The predicates are defined for any such matrix representation. For the
source's proper matrix height, specialize `ρ` to a closed matrix realization
as in I.1 and `RationalWeights`; closedness and any additional compatibility
with the chosen compact subgroup must be supplied when an eventual proof
needs them. No comparison with central valuation coordinates is built into
the target or used to replace this full height.

## Exact I.1 and VI.3 measures

Put `νM = RationalPointFamily.leviRationalNormCharacters i ν I`,
`omegaπ = discreteSeriesClass CM hCM mu π hsq`, and
`O = discreteSeriesOrbit CM hCM mu νM omegaπ`. These are the existing
discrete-series class and unitary unramified twist orbit on the literal Levi.
Every target fixes

```text
rhoX = standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex
dO   = discreteSeriesOrbitMeasure νM CM hCM mu omegaπ rhoX.
```

`rhoX` transports `rationalUnitaryUnramifiedCharacterHaar` through
`standardLeviUnitaryCharacterHomeomorph I`, the specialization of
`unitaryUnramifiedCharactersHomeomorph` along
`leviRationalPointHomeomorph i ν I`. I.1 fixes mass-one Haar on the
split-component character group and local measure preservation under
restriction. Consequently, `rhoX` has mass `|ker restriction|`, where the
kernel is that of `rationalUnitaryUnramifiedCharacterRestrict s`.

The imported `StandardLeviCharacterMeasure` adapter proves equality of `dO`
with `standardLeviNormalizedDiscreteSeriesOrbitMeasure`, the transported
source-normalized measure, and proves

```text
dO = |self-twist stabilizer of omegaπ|⁻¹ • (orbitMap omegaπ)_* rhoX
dO(O) = |ker restriction| / |self-twist stabilizer of omegaπ|.
```

These cardinality formulas are derived from the finite-cover conventions.
VI.3, p.302, requires local measure preservation for the twisting map;
the adapter's local-preservation theorem implements that convention.
The measures are generally not probability measures.
The finite-measure result reuses
`isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure` from
`RationalOrbitIntegration` through transport. No orbit finiteness proof or
normalization is introduced in this target module.

The quotient Haar `mu` in `hsq`, the weight denoted `mu(omega)` in
Waldspurger's integral, and the orbit measure `dO` have distinct roles.
In Lean the weight is the function `W = standardLeviPlancherelWeight ...`;
`mu` is the central-quotient Haar; integration over `O` uses the fixed `dO`.

## The three new targets

`StandardLeviPlancherelWavePacketMembershipStatement` asserts, for every
`q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π`, both:

1. for every `g : rationalPoints G`, the function
   `omega ↦ W omega * rationalInducedOrbitCoefficientMap ... q omega g`
   is integrable with respect to `dO`;
2. `standardLeviPlancherelWavePacket ... rhoX q` belongs to
   `schwartzSubmodule (rationalXi hKc hPK) (rationalHeight ρ)`.

The imported packet wrapper is definitionally the existing
`rationalInducedOrbitWavePacket` with this actual weight. Its proved
pointwise formula is the integral

```text
packet q g = ∫ omega : O, W omega *
  rationalInducedOrbitCoefficientMap ... q omega g ∂dO.
```

Membership is full Schwartz membership. By
`mem_schwartzSubmodule_iff` and `mem_levelSubmodule_iff` in `Basic`, it
requires a compact open bi-invariance subgroup and
`∀ r : ℝ, nu (rationalXi hKc hPK) (rationalHeight ρ) r (packet q) < ⊤`.
The displayed `K` supplies a nonempty compact-open subgroup class for this
unpacking; the membership conclusion does not prescribe the bi-invariance
subgroup to be all of `K`.

`StandardLeviPlancherelWavePacketContinuityStatement` asserts the existence
of

```text
synth : rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π →L[ℂ]
  RationalSchwartzSpace hKc hPK ρ
```

such that `synth q g` equals exactly the displayed integral for every `q`
and every actual group point `g`. The integrand uses
`OrbitSectionSpace.toSections` with the canonical actual standard-parabolic
arguments to recover the existing smooth section. It is not a new model
of orbit sections. The codomain concludes Schwartz membership while the
continuous linear map concludes continuity and complex linearity. No
Schwartz-valued lift, output estimate, or continuity of synthesis is an
input. Integrability is explicitly included in the separate membership
target.

`StandardLeviPlancherelWavePacketSourceNormalizedStatement` is the
conjunction of these two component targets with identical data. This is
the joint principal target: the measure scale is fixed, the actual weight
is fixed, integrability is explicit, and membership and continuity are
conclusions. It contains no coefficient Xi bound, weak-constant-term
formula, positive-part estimate, or uniform output-seminorm bound as an
extra premise. Square integrability is the inducing-representation
hypothesis; the conditional density inputs listed above remain visible.

## Topology and source correspondence

VI.3, p.301, first gives each product fixed coefficient space its canonical
finite-dimensional topology, equips its tensor product with
`C∞(Im X(M))` with the product topology, takes the subspace of sections,
and then the inductive limit over compact open levels.
The target uses the already constructed ordered-derivative section
seminorms, fixed levels, and locally convex inductive-limit topology of
`OrbitSectionTopology` and its rational adapter. The codomain uses the
existing all-real Schwartz seminorms and locally convex inductive-limit
topology of `Basic` and `RationalWeights`.

Finite dimensionality is already proved by
`finiteDimensional_orbitSectionFixedCoefficients` in
`OrbitSectionFixedTensor` and
`finiteDimensional_rationalOrbitSectionFixedCoefficients` in
`RationalOrbitSectionFiniteProductTopology`. The faithful section tensor
and coordinate maps, independent scalar ordered-derivative and
basis-coordinate tensor topologies, and finite-product level and total
topologies are also existing constructions.

Their comparison remains open in the published targets
`SmoothTensorBasisIndependenceStatement`,
`OrbitSectionLevelFiniteProductTopologyStatement`,
`OrbitSectionTotalFiniteProductTopologyStatement`,
`OrbitSectionFiniteProductTopologyStatement`,
`RationalOrbitSectionLevelFiniteProductTopologyStatement`,
`RationalOrbitSectionTotalFiniteProductTopologyStatement`, and
`RationalOrbitSectionFiniteProductTopologyStatement`.
Those are separate obligations, not assumptions added to these targets.
Accordingly, proving the new continuity target in the existing topology
would still require the comparison to identify it with the literal
topological assertion of the source.

Proposition VI.3.1, p.302, concludes membership for every smooth orbit
section and continuity of the packet map. The Lean continuity target also
records the complex linearity implicit in the source's integral. The
integrability clause makes the integral's analytic meaning explicit;
it prevents reliance on the default value of a nonintegrable Bochner
integral. These formulations use existing conditional constructions and
are targets for those conclusions, not a claim that all their proofs
or prerequisites are complete.

## Why central-direction decay is insufficient

The source's proof on p.302 seeks a bound for every real output seminorm
by finitely many constant-coefficient parameter derivatives at each fixed
coefficient level. After Cartan chamber reduction, p.303 separates the
constant term along a suitable proper parabolic into its weak and positive
parts and also treats the bounded-chamber region.

Central Fourier decay on p.303 gives arbitrary polynomial decay in
`H_G(g)`. On p.304 the height is controlled by that central coordinate
only on the bounded-chamber region. The published actual-weight estimate
`exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow`
likewise supplies central-direction decay under its displayed coefficient
Xi-bound hypothesis. Such a bound does not control the full matrix height
along general noncentral chamber directions, and supplies neither the
new membership target nor continuous synthesis.

For the weak part, p.304 invokes V.1.1 and V.2.3: the normalized
`c`-functions are regular on the unitary locus and express the weighted
weak constant term as a finite sum of lower-Levi packets. Induction on
semisimple rank supplies arbitrary lower-Levi decay; the Xi comparison
II.1.1 absorbs the remaining polynomial loss.

For the positive part, p.305 uses the exponential chamber decay of
VI.2.3 together with central Fourier decay and the height comparisons.
The exponential bound absorbs every remaining polynomial chamber factor.
Together these steps give the all-real seminorm estimates needed at
each level, and hence continuity after the topology comparison.
These weak-constant-term, positive-part, and full output-seminorm
arguments remain proof obligations; none is silently assumed here.

## Reused results and limits of this module

The section, coefficient, orbit, weight, integral and topological spaces
are imported constructions. Character/orbit measure comparisons,
stabilizer finiteness under `hindex`, fixed-coefficient finite
dimensionality, and
`standardLeviPlancherelParabolic_eq` are existing proved results. The last
identifies the dynamic scalar parabolic with this actual standard
parabolic; the dynamic-Levi pullback remains internal to the imported
weight. This module adds only the three related Prop-valued targets.

Stating these targets does not prove VI.3.1, discharge `hindex` or the
conditional scalar/density hypotheses, prove the topology comparisons,
or establish semistandard/global synthesis, isometry, inversion, or
Plancherel. It preserves the scalar, inverse-regularity, density, and
Hermitian-adjunction work without changing their declarations.
