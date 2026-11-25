# Actual standard source integral and product-core comparison

This derived module identifies the actual
source-normalized semistandard orbit form at the standard Levi with
`standardLeviPlancherelOrbitProductCore` and its integral formula.

## Source and data

Waldspurger (2003), registered `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
VII.2, printed p.319 (PDF p.85), defines the inverse-formal-degree
coefficient pairing and its density-weighted orbit integral. I.1 and
VI.3 supply the source measure and normalization already compared in
`RationalSemistandardStandardPacketComparison`. The exact Lean
standard/intrinsic adapters are derived consequences of those existing
constructions.

All declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard.StandardFormComparison`.
The field and representation universes are independent. The field is an
arbitrary nonarchimedean local field and the ambient group is affine,
locally of finite type and connected reductive. The maximal split torus,
generic cocharacter, standard root subset and standard cocharacter
presentation remain explicit. No splitness, quasisplitness or
characteristic-zero assumption is imposed on the ambient group.

The coefficient compact picture is `standardCompactData`, with its
actual compactness and Iwasawa-pair inputs. The central subgroup is
`standardLeviModel.splitCenter a`, the actual point image of an algebraic
split component `a`. The supplied measure on this literal central
quotient is Haar and inverse invariant, with the displayed Borel
measurable structure. The exact finite-index input is
`(RenardCartan.splitValuationImage a).FiniteIndex`.

## Actual constructor and equality

`standardCore` is exactly the published
`standardLeviPlancherelOrbitProductCore`, specialized at these source
inputs and at the actual scalar data in `OrbitPacketData`. It retains
all primitive continuation, domain, generic irreducibility and full
unitary inverse-regularity prerequisites of that data. Its additional
scalar inputs are precisely nonvanishing of the actual
`StandardSourceComparison.standardScalar` and nonnegative real values
of its inverse at every unitary unramified character. The existing
product core uses the resulting dense positive locus; this module does
not require the Plancherel density to be strictly positive everywhere.

The imported core's additional group-finiteness input remains explicit:

`Finite (M / (commonNormKernel model.normCharacters sup model.splitCenter a))`.

Here `M` is the actual literal standard Levi. This is the exact central
norm quotient, not a freely supplied finite set. Finiteness of the
unramified self-twist stabilizer is supplied by the already proved
`SourceMeasure.finite_literalDiscreteSeriesStabilizer` at the actual
valuation-image input. Finiteness and positivity on nonempty open sets
of the actual source character Haar are proved locally from
`SourceMeasure.unitaryCharacterHaar`; they are not extra assumptions.
The original I.1 scale and reciprocal self-twist factor are unchanged.

`weightedOrbitForm_eq_standardCore_inner` states, for every two actual
smooth orbit sections, that `SourceForm.weightedOrbitForm` equals the
inner product of this `standardCore`. The left side is the actual
integral of `SourceForm.orbitDensity` times `SourceForm.pairing` against
`SourceMeasure.normalizedOrbitMeasure`. In particular the first argument
is conjugate linear and the coefficient pairing is the existing
inverse-formal-degree induced tensor pairing. The equality does not
select an abstract positive form or use an assumed synthesis isometry.

## Implemented proof and boundary

The constructor directly specializes the existing standard core, with
explicit identical quotient instances. The integral proof invokes
`standardLeviPlancherelOrbitProductCore_inner` at the same data, rewrites
the source orbit measure by
`StandardPacketComparison.orbitMeasure_eq_standard`, and applies
`StandardSourceComparison.density_eq_standard` pointwise under the
integral. The remaining pairing, compact-picture and core comparisons
are definitional, including equality of proof inputs. Thus the proof
identifies the exact source-normalized pairing and formal-degree
normalization in this standard specialization.

This comparison proves no general model/representative/compact
independence and no new global positivity, Schwartz estimate or
Plancherel isometry. Those substantive targets and the invariant-family
restriction are separate. The central norm quotient finiteness and all preceding scalar
inputs remain visible conditional boundaries of the imported core.
