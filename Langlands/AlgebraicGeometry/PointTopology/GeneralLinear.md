# General linear point topology comparisons

This unit constructs the comparison between the published evaluation topology
on actual points of the general linear group scheme and the existing topology
on matrix units `GL n S`. It uses the entry and inverse-entry coordinate ring
from `Langlands.GroupScheme.GeneralLinear` and the actual affine scheme-point
homeomorphisms from `Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps`.

## Source and provenance

This is a derived specialization of the affine evaluation construction in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Proposition 2.1 and its proof, printed pages 2–3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad describes the topology through evaluation of every coordinate-ring
element, and proves that polynomial coordinate presentations yield that same
topology. This unit applies that construction to the Library's explicit
matrix-and-inverse presentation; the named GL scheme and its classification
maps come from the imported Library, rather than a new choice of scheme.

The relative formulation uses commutative rings `R` and `S` in a common arbitrary
universe, with an `R`-algebra structure on `S`. Only `S` has a topology. Coefficients
from `R` evaluate to constant functions with values in `S`, so the construction
needs no topology on `R`. Setting `S = R` recovers the absolute formulation.
The finite index type `n : Type` has `Fintype` and `DecidableEq` instances and may
be empty. No separation, field, local-ring, or open-unit hypothesis is imposed.

## Constructions and exact maps

All declarations lie in
`Langlands.AlgebraicGeometry.PointTopology.GeneralLinear`.

- `continuous_point` proves continuity from
  `AlgPoint R (CoordinateRing n R) S` to `GL n S` for any topology on `S`.
  Its map is `f ↦ point f.toAlgHom`, specializing the universal invertible matrix.
- `continuous_classify` proves continuity in the reverse direction for
  `IsTopologicalRing S`. Its map sends `g` to the existing algebra homomorphism
  `classify g`, viewed as an evaluation-topologized `AlgPoint`.
- `algPointHomeomorph` packages the existing algebraic equivalence `homEquiv`
  as a homeomorphism with those maps. The domain is actual algebra
  homomorphisms with the published evaluation topology.
- `schemePointHomeomorph` is a homeomorphism from
  `RingPoint R (groupScheme n (CommRingCat.of R)).X S` to `GL n S` for
  `IsTopologicalRing S`. Its domain consists of actual morphisms over `Spec R`
  from `Spec S` into the imported general linear group scheme, with the
  existing affine scheme-point topology. It composes
  `spectrumRingPointHomeomorph`, `specPointHomeomorph`, and
  `algPointHomeomorph`; it introduces no new point topology.
- `schemePointHomeomorph_eq_point` identifies its value at a scheme point `p`
  with `point (affineRingPointEquiv R (CoordinateRing n R) S p)`.
  `schemePointHomeomorph_apply` proves that this is exactly the existing
  `Langlands.GroupScheme.GeneralLinear.affinePointsEquiv` applied to `p`.
  Consequently this homeomorphism uses the published multiplicative point
  comparison, not an unrelated bijection of carriers.

The matrix-unit topology is Mathlib's topology on units of the matrix ring.
It records the entries of both the matrix and its inverse. This distinction
matters over arbitrary topological rings; it is also the convention in Conrad's
opening discussion of section 3, printed page 3, for `Gm`. The construction
does not need the inclusion of units into matrices to be an open embedding.

## Implemented continuity and identification arguments

Forward continuity uses `Units.continuous_iff`: each matrix entry and inverse
entry is evaluation at the corresponding image of a polynomial variable in
the coordinate ring. These evaluation maps are continuous by construction.
For backward continuity, lift an arbitrary coordinate-ring element to a
polynomial. Its value at `classify g` is that polynomial evaluated at the entries
of `g` and `g⁻¹`, with each coefficient mapped to a fixed element of `S`.
Inversion in the existing unit topology, coordinate projections, and polynomial
evaluation are continuous, giving continuity of every evaluation map.
These arguments also apply when `n` is empty.

The first scheme-map identity follows from the actual affine spectrum
homeomorphism's underlying-map formula. The final identity writes a scheme
point through `affineRingPointEquiv` as the spectrum of an algebra map and uses
the published `affinePointsEquiv_map` formula. Both identities therefore compare
actual scheme morphisms and the existing algebraic classification maps.

This focused construction supplies the scheme/matrix topology bridge. General
nonarchimedean group properties, second countability, subgroup results, and the
remaining sections of the paper are separate obligations.
