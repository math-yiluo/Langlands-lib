# Rational normalizer representatives of integral rho opposition

This internal construction starts with an actual affine group scheme `G`
over a field `k`, a commutative group scheme `T`, a supplied homomorphism
`j : T → G` whose underlying scheme morphism is a monomorphism, and an
actual integral root datum `P` on the character and cocharacter lattices
of this same `T`. The hypothesis `IsRootDatumOf j P` includes equality
with the actual lattice pairing, the exact root set, and rational
normalizing representatives of all root reflections. No existence of
these supplied objects is asserted here.

The published inclusion `IsRootDatumOf.abstractWeylImage_le` lifts every
abstract Weyl element to an actual rational normalizer point. The
construction `weylRepresentative` chooses such a point, and its action
on the entire integral character lattice is the prescribed Weyl action.
This step needs neither reductivity nor maximality nor a finite index
set, and uses the inclusion rather than equality of the two Weyl images.

For the remaining constructions the root index set is finite and supplied
with a `Fintype` structure. Its universe may differ from that of `k` and
the group schemes. The integral polarization takes weights to actual
cocharacters. If a rational Weyl representative sends a weight `x` to
`-x`, invariance of the canonical root form and its identification with
the pairing against the polarization show that the inverse normalizing
automorphism sends this cocharacter to its negative. Composing with the
forward automorphism gives the same negation for the forward action.
This is an integral argument on the full lattices.

Now additionally supply a base `b` of the reduced datum and assume the
coroots span the entire integral cocharacter lattice. The previously
constructed `IntegralWeylVector.opposition` provides an actual Weyl
element sending its integral rho to negative rho.
`oppositionRepresentative` lifts exactly that element to a rational
normalizer point. Its character action sends rho to negative rho, and
therefore sends negative rho to rho, as required by the negative-rho
unit-cell construction. The character action convention is inverse
precomposition by the normalizing automorphism.

The polarization of this same rho is generic for the original embedding
`j`, by the published coroot regularity and polarization criterion. The
chosen normalizing point reverses this actual cocharacter. The identity
`groupHom_cocharacterAut_comp` identifies its inner conjugation with the
forward torus action, and negation in the cocharacter lattice is the
exact parameter inversion used by `Dynamic.oppositeCocharacter`.
Consequently conjugating any supplied representative `i : H → G` of
this dynamic parabolic by the constructed point represents its opposite.
The final statement concerns the full subgroup functors on every
relative test scheme, including nonaffine and nonreduced tests; it follows
from the published isomorphism transport of dynamic parabolics and their
representatives, without restricting to rational test points.

The input group need not be reductive and the supplied torus need not be
split or maximal for these conclusions. Existence of suitable structural
data, the Borel property of the selected dynamic parabolic, a Bruhat
covering, the covariant coordinate and the entire induced-space
Steinberg irreducibility remain separate obligations of the host task.
