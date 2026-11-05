# Regular integral characters and actual torus centralizers

This internal construction works with an affine group over a field, an actual
commutative subgroup, and a supplied finite integral root datum on its actual
character and cocharacter lattices. `IsRootDatumOf` identifies its pairing and
root set with the actual ones. No root datum or subgroup is asserted to exist.

For a supplied character `x` nonzero on every coroot, the definition
`genericCocharacterOfRegularWeight` constructs an actual generic cocharacter
together with its proof of genericity. Its value is Mathlib's integral
polarization `P.Polarization x`, the sum of the coroots weighted by their
pairings with `x`. No scalar extension is needed.

The canonical root form evaluates on a root as the pairing of that root with
the polarization. Twice this value is the product of the root's positive
self-pairing under the form and the value of `x` on its coroot. The latter
is nonzero by regularity. The self-pairing is a sum of integral squares
including the square of two, so it is positive. Thus the resulting cocharacter
pairs nontrivially with every actual root.

Suppose a supplied rational normalizing point has the character action of a
supplied abstract Weyl element and fixes `x`. Weyl invariance of the canonical
form and the exact character/cocharacter pairing convention show that its
inverse torus automorphism fixes the polarization. Perfectness of the integral
pairing detects equality on the full cocharacter lattice. Composing with the
forward automorphism shows that it too fixes the polarization.

For a connected reductive group and an actual maximal split torus, the
published normalizer/cocharacter centralizer criterion therefore places the
point in the dynamic centralizer of this generic cocharacter. The published
exact `genericCentralizer` theorem identifies this with the whole torus
centralizer. The last theorem obtains the needed abstract Weyl representative
from a supplied equality between the actual and abstract integral Weyl images.

The proof retains this Weyl-image equality as an explicit hypothesis. It
does not prove the general Weyl comparison, construct negative rho or a
representation, or prove a Bruhat covering or Steinberg irreducibility.
Its provenance is the implemented internal argument from Mathlib's integral
canonical form and polarization and the published actual normalizer,
pairing, and generic-centralizer interfaces.
