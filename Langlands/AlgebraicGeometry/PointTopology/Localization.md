# Localization and principal-open point topologies

This unit constructs the equivalence between points of an actual localization
algebra and the locus of algebra maps sending its denominators to units. It
then constructs a homeomorphism using continuity of multiplication and the
subspace topology on units. For a single inverted element, open units make the
actual restriction map an open embedding.

## Source and provenance

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), section 3, printed page 4, opening discussion and the
principal-open step of Proposition 3.1. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad identifies points of `Spec A[f⁻¹]` with the locus where `f` has unit
value, and explains that the topology also controls the inverse of that value.
The proof of Proposition 3.1 makes this locus an open subspace when units are
open and inversion is continuous in their subspace topology.

The present general multiplicative-set and relative algebra-map formulations
are derived extensions of that argument. They reuse Mathlib's actual
`IsLocalization` and localization lift, and the Library's existing `AlgPoint`
evaluation topology. A fraction has one numerator and one denominator, so the
same coordinate argument works without finite generation. It needs only
continuous multiplication, rather than all the topological-ring axioms.
The source's principal-open case is a direct specialization. This is the
algebra-map step toward the actual nonaffine scheme topology; the scheme-host
comparison and gluing remain separate obligations.

## Objects, maps, and hypotheses

All declarations are in
`Langlands.AlgebraicGeometry.PointTopology.AlgPoint`. The coefficient ring `R`,
coordinate ring `A`, value ring `S`, and localization ring `L` are commutative
rings in four independent universes. There are `R`-algebra structures on `A`,
`S`, and `L`, an `A`-algebra structure on `L`, and `IsScalarTower R A L`.
For a submonoid `M : Submonoid A`, assume `IsLocalization M L`.
Only the value ring `S` is topologized.

`LocalizationLocus M` is the actual subtype of `AlgPoint R A S` consisting of
maps `p` with `IsUnit (p m)` for every denominator `m : M`. Its topology is the
subspace topology from the existing evaluation topology, with no extra
assumed properties.

`localizationPointEquiv M` maps a point of `L` to its restriction along
`Algebra.algHom R A L`, together with its unit-valued-denominator proof.
Its inverse is Mathlib's `IsLocalization.liftAlgHom` applied to the given
algebra map and those unit proofs. The inverse laws use the localization
universal property. `localizationPointEquiv_apply` and
`localizationPointEquiv_symm_algebraMap` give the restriction and extension
formulas on original coordinates.

`localizationPointHomeomorph M hS` equips this equivalence with continuity in
both directions. It assumes `ContinuousMul S` and
`hS : IsEmbedding (Units.val : Sˣ → S)`. Thus it needs the unit subspace-topology
condition, independently of any openness condition. Its underlying forward
map is the same actual restriction map. The related
`range_precomp_localization` computes the range of restriction exactly, and
`isEmbedding_precomp_localization` proves that restriction into all `A`-points
is an embedding under these same topological hypotheses.

For an element `f : A`, `unit_powers_iff` identifies the all-denominator
condition for `Submonoid.powers f` with `IsUnit (p f)`.
`isOpen_unitLocus` proves that this locus is open under `IsOpenUnits S`.
`isOpenEmbedding_precomp_away` proves that the actual restriction map from
any `L` with `IsLocalization.Away f L` is an open embedding when multiplication
is continuous and `IsOpenUnits S` holds. Mathlib's `IsOpenUnits` means that the
unit inclusion is an open embedding; it includes both open unit set and
subspace topology, the latter being the continuous-inversion condition in the
source. No local-ring, separation, field, nontriviality, finite-type, or
finite-presentation hypothesis is imposed. In particular, this construction
retains the empty point-locus cases, including inversion of zero into a
nontrivial value ring.

## Implemented continuity argument

Restriction is the published continuous precomposition map, followed by its
continuous lift to the subtype. For the inverse, fix one coordinate `b : L`.
Mathlib's localization property supplies `a : A` and `m : M` with
`b * algebraMap A L m = algebraMap A L a`.
`localizationPointEquiv_symm_apply` applies the lifted algebra homomorphism to
this identity and cancels the unit denominator to obtain

`lift(p)(b) = p(a) * ((p(m) as a unit)⁻¹).val`.

The map from the locus into `Sˣ` selecting the unit over `p(m)` is continuous
because the unit inclusion is an embedding and its composite into `S` is a
continuous evaluation map. Inverse-unit evaluation and multiplication are
continuous, so the displayed formula proves continuity at every coordinate
of `L`. The universal property of the evaluation topology then gives
continuity of the lifted point map. This argument does not assume any desired
topological conclusion through a structure field.

For a principal localization, the range formula and `unit_powers_iff` identify
the range with the inverse image of the unit subset under evaluation at `f`.
The unit subset is open under `IsOpenUnits`, proving the claimed open
embedding. The general submonoid result asserts an embedding, with no claim
that an arbitrary intersection of such unit loci is open.

The later use of a local value ring is to show that points land in affine
charts of a chosen open cover. That coverage result, arbitrary affine-open
embeddings on actual scheme points, and the gluing and other conclusions of
Proposition 3.1 are retained as separate obligations.
