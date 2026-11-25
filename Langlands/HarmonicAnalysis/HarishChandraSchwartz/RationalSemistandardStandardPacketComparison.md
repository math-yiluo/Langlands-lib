# Actual standard source measure and wave-packet comparison

This derived module identifies the actual
semistandard coefficient normalization, source Haar and orbit measure,
and raw wave packet with their existing standard-Levi specializations.

## Source

Waldspurger (2003), registered `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
I.1, printed p.239 (PDF p.5), final paragraph, supplies the source
character-Haar normalization. VI.3, printed pp.302–305 (PDF pp.68–71), supplies the
orbit wave packet and its normalization. The standard/intrinsic adapter
is an internal consequence of the published source constructions, rather
than a separately named assertion in the paper.

## Data and declarations

Declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard.StandardPacketComparison`.
They use the actual `standardLeviModel`, `standardCompactData`, and the
genuine `StandardSourceComparison.presentation`. Field and representation
universes remain independent; the ambient connected reductive group need
not be split, quasisplit or in characteristic zero.

`coefficient_eq_standard` identifies `SourcePacket.coefficientMap` with
`rationalInducedOrbitCoefficientMap` at the same compact picture. The
normal central subgroup, quotient measurable space, quotient Haar measure
and square-integrable inducing representation are identical. The equality
includes the actual normalized coefficient map, not only its domain.

For source measures and packets the subgroup is the actual split-center
point image `standardLeviModel.splitCenter a` for a supplied algebraic
split component `a`. Both this image and the scheme-point image have their
normality instances, and the literal quotient has its Borel measurable
space and displayed Haar measure. The finite-index premise is exactly
`(RenardCartan.splitValuationImage a).FiniteIndex`; it is not an arbitrary
finite-orbit assumption.

* `standardCharacterHaar` transports the actual
  `rationalUnitaryUnramifiedCharacterHaar a ...` through the existing
  `RationalPointFamily.leviRationalPointHomeomorph`. Its normalization is
  the original I.1 scale, without division by its total mass.
* `characterHaar_eq_standard` proves that
  `SourceMeasure.unitaryCharacterHaar` is this same measure.
* `orbitMeasure_eq_standard` identifies the transported source orbit
  measure with `discreteSeriesOrbitMeasure` at that character Haar. The
  reciprocal cardinal of the actual unramified self-twist stabilizer is
  retained by the imported orbit-measure definition and comparison.
  Finiteness of this stabilizer is proved from the exact valuation-image
  finite-index input through
  `SourceMeasure.finite_literalDiscreteSeriesStabilizer`, rather than
  assumed separately.
* `standardPacket` is the existing
  `rationalInducedOrbitWavePacket` with this source character Haar and
  `StandardSourceComparison.standardDensity`. The latter is precisely
  the actual `standardLeviPlancherelWeight` at the primitive scalar data.
* `packet_eq_standard` identifies `OrbitPacketData.packetLinear` with this
  actual standard packet at every input section and ambient group point.

The scalar prerequisites are retained in `OrbitPacketData`: the existing
relative-reflection and central-split-character assertions; scalar
compact, compactness and both factorizations; the forward/reverse
continuations and their open nonempty full-domain-contained regions;
the generic irreducibility region; and inverse regularity on the unitary
locus. These comparisons prove no new scalar regularity or positivity.
The scalar compact and the coefficient compact remain independent.

## Proofs and boundary

Coefficient-map equality and character-Haar equality reduce to the
published definitions and equality of proof inputs. The source
orbit-measure comparison specializes
`SourceMeasure.normalizedOrbitMeasure_eq`. Packet equality rewrites this
measure and uses pointwise multiplication of the actual density equality
and coefficient equality inside the Bochner integral. Pointwise
integrability and linearity of the source packet were proved in
`RationalSemistandardWavePacket`; this module preserves them through the
exact comparison.

No new Schwartz membership estimate is asserted. Standard membership
and continuous-synthesis targets are those of
`StandardLeviPlancherelWavePacketSchwartz`. General semistandard
model/representative/compact independence is separate, and the actual
standard orbit-product-core comparison is
`RationalSemistandardStandardFormComparison`.
