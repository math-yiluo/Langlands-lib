# Root-span kernels and restrictions of rational characters

Author: Worker 37.

This is an internal derivation from the published definitions of rational
characters, inner automorphisms, normalizing points, rationalization and the
relative-root span. No root-system existence result is assumed or proved.

Over any base scheme, an inner automorphism fixes every rational character
as a group-scheme morphism: on every test scheme, a character sends a
conjugate to the conjugate of its value in the commutative multiplicative
group. The normalizer therefore fixes each character obtained by restricting
a rational character of the ambient group to the torus.
`torusCharacterRestrict` records this restriction in the existing torus
character lattice.

Over a field, for a split torus embedded by a monomorphism into an affine
group, the action of a normalizing point on `relativeRootSpan i` is the
identity if and only if its character action fixes every actual relative
root. The forward direction uses injectivity of rationalization on the
split torus's character lattice; the reverse direction uses linear
induction on the span of the roots.

The final two lemmas have an explicit extra premise: the images under
rationalization of the relative roots, together with the restrictions of
all rational characters of the group, span the entire rational character
lattice of the torus. Under this premise, a normalizing point fixing every
root acts identically on every character. Indeed, its rational linear
action fixes both classes of generators. Injectivity of rationalization
then recovers equality of characters. This identifies the root-span and
full-character kernels on normalizing points under the stated premise.

The spanning premise is not established here, including for a connected
reductive group with a maximal split torus. These supporting results alone
do not prove `RelativeRootSystemStatement`, construct coroots, or identify
the image with a root-system Weyl group.
