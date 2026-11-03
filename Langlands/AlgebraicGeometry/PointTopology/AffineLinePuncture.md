# The actual D(t) open and the dual-number point

This derived construction supports the correction of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Remark 3.3 on
printed page 5. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The correction's assertions about the origin's complement, nilpotent image
containment and coverage are separate statement/proof obligations.

## Schemes and actual points

Let R and S be commutative rings in the same arbitrary universe, with an
R-algebra structure on S. No topology, locality, nontriviality or faithfulness
is assumed. `affineLinePuncturedOpen` is the actual basic open D(t) in
Spec(R[t]), using `MvPolynomial Unit R` and t = X().
`affineLinePuncture` gives that open subscheme its actual morphism to Spec R,
and `affineLinePunctureι` is its actual relative open immersion. They reuse
`openOver` and `openOverι`, not an auxiliary set of coordinates.

`range_subset_affineLinePuncturedOpen_iff` says that the whole underlying
image of an actual S-valued affine-line point lies in D(t) if and only if its
coordinate under `affineLinePointEquiv` is a unit of S. Under the inverse
coordinate equivalence, the underlying map is comap of evaluation at that
coordinate. Containment in D(t) says that no prime ideal contains the
coordinate. A nonunit lies in a maximal ideal, and a unit lies in no prime
ideal, proving the equivalence even for the zero ring.

`range_affineLinePuncture_points` then identifies the exact image on actual
relative S-points with the unit-coordinate locus. The reverse inclusion uses
the existing universal lift of a scheme map whose entire image lies in an
open subscheme. These are intrinsic laws of the chosen open construction.

## An actual local Artinian value ring

For a field K, the value ring is Mathlib's actual dual-number ring
`DualNumber K = TrivSqZeroExt K K`. Mathlib supplies its commutative-ring,
K-algebra and local-ring instances. `dualNumber_isArtinianRing` proves its
Artinianness: the first and second coordinate maps give an injective K-linear
map to K × K, an Artinian K-module. An explicit compatible scalar tower
transfers the descending-chain condition to ideals of the dual-number ring.
The tower compatibility is checked on both coordinates of the multiplication.

`dualNumberAffineLinePoint` is the actual relative scheme point obtained by
applying the inverse affine-line coordinate equivalence to epsilon. Its
coordinate is epsilon. `dualNumber_eps_ne_zero` uses its second coordinate,
which is 1. `dualNumber_eps_not_isUnit` uses Mathlib's unit criterion for a
trivial square-zero extension: a unit must have a unit first coordinate,
whereas epsilon has first coordinate zero.

These constructions and coordinate laws make no claim that nilpotence is
factorization through the zero closed subscheme. The separate correction
will distinguish that factorization from containment of the underlying
image in the origin, and will test the printed local Artinian coverage claim
using this actual point.
