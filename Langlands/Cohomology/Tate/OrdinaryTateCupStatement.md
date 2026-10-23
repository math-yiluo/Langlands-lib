# Comparison of ordinary and Tate cup products

Author: Worker 45.

`Langlands.Tate.OrdinaryTateCupLaws` states that the published actual ordinary
cochain cup and the published dimension-shifted Tate cup agree under the
canonical comparison in every pair of nonnegative degrees. It quantifies over
a commutative ring `R`, a finite group `G`, three representations `A,B,C`, an
equivariant bilinear pairing `φ : A × B → C`, natural numbers `p,q`, and actual
ordinary cohomology classes in those degrees. All carriers share an arbitrary
universe `u`. In particular the statement permits the lifted integer scalar
ring used by the local class-formation application.

The left side first forms `ordinaryCup φ p q a b` in ordinary degree `p+q`,
then applies `ordinaryToTate C (p+q)`. The displayed `tateDegreeIso` transports
its target from the integer cast of the natural sum to the sum of the integer
casts. The right side applies `ordinaryToTate` to the two inputs separately
and uses the actual integer-degree `cup φ`. The coefficient object is `C` on
both sides, and the degree transport has the indicated forward orientation.

`ordinaryCup` is the descent of the explicit inhomogeneous cochain formula
with the ordered prefix acting on the second coefficient. `cup` is the
dimension-shifting construction from the invariant pairing modulo norms,
using actual Tate connecting maps and tensor products. Neither product is an
assumed bilinear operation. In positive degrees `ordinaryToTate` is the inverse
of Mathlib's ordinary/Tate cohomology identification. In degree zero it sends
an invariant class to its class modulo the actual norm image. Thus the
statement includes `p=0`, `q=0`, and `p=q=0`; it does not assert that the
degree-zero comparison is an isomorphism.

There are no flatness, acyclicity, chosen splitting, cup-law or comparison-law
premises. The anticipated proof can use the proved scalar splittings of the
canonical shift sequences to obtain tensor exactness internally. The target
does not concern negative ordinary degrees, since ordinary cohomology here is
indexed by natural numbers.

This is an internal comparison target for two independently constructed
operations on Mathlib's actual cohomology. Serre, *Local Fields* (1979),
VIII §3, Proposition 5 and its uniqueness argument, printed p.131 (PDF p.137),
fixes invariant normalization, coefficient naturality, and the two tensor
boundary signs for Tate products. The discussion of bilinear pairings on
printed p.132 (PDF p.138) supplies the coefficient-pairing convention. Those
pages concern integral finite-group Tate cohomology; they do not literally
state this commutative-ring Lean comparison with its explicit degree transport.
The internal provenance is the agreement forced by invariant normalization
and connecting-map laws: ordinary classes can be reduced to degree zero by
the canonical coinduced shift sequences, and the two constructions then use
the same boundary signs. Passage from tensor products to `φ` uses its tensor
map and coefficient naturality. This paragraph explains the target's
provenance, not a proof supplied by this file. The exact bound proof and its
independent validation are separate work.
