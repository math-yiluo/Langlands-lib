# Local quasi-isogenies in the rational Hom sheaf

Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), Chapter 2,
Definition 2.8, printed p.52 (PDF p.67), defines a quasi-isogeny as a
section of the rational Hom sheaf that becomes an integral isogeny after
multiplication by a suitable power of p on a neighbourhood of each point.
Definition 2.6, printed p.51 (PDF p.66), gives the isogeny condition.

This module gives the distinguished-scalar analogue for the existing
finite-coordinate formal O-modules over an affine base Spec R. It uses
the rational Hom sheaf constructed in `RationalHomSheaf`, and the actual
affine point-functor isogeny condition from `FiniteKernel`: affine fppf
local lifting and a represented finite locally free kernel. The
comparison of that affine condition with epimorphisms of fppf sheaves
between general p-divisible groups remains outside this construction.

`OpenIntegralHom M N U` is the actual integral formal Hom over
the structure-sheaf section algebra Γ(U). `RationalSection.ofIntegral`
first rationalizes the formal map and then applies the sheafification
unit. Restricting it agrees with the coherent coefficient restriction
of the integral map. Those coefficient restrictions preserve isogenies:
base change preserves the actual kernel and local lifting, and the
identity-coordinate comparison isomorphisms transport the resulting
arrow.

`RationalSection.IsLocallyScalarIsogeny π z` requires, at each x in U,
an open neighbourhood V contained in U, an exponent n in the natural
numbers, and an actual integral isogeny f over Γ(V), such that
π^n times z restricted to V is the image of f in the rational sheaf.
The scalar π is mapped from O to F before it acts. Neither a global
integral representative nor a common bound on these exponents is required.

The implemented restriction proof intersects a witnessing neighbourhood
with the smaller open, then restricts its integral isogeny and the
equality in the rational sheaf. The converse locality lemma assembles
this pointwise condition over any open cover. Integral isogenies give
examples with exponent zero.

`LocalQuasiIsogeny F π M N U` retains a rational section satisfying this
local condition, together with the hypotheses that π is nonzero in F
and M and N are π-divisible in the previously defined affine sense.
In particular π is nilpotent on the base. Restriction preserves these
objects and satisfies the identity and composition laws.

The provenance is derived from the cited local definition. O is any
commutative ring, F is an O-algebra field, and π is a distinguished
scalar; no local-field, uniformizer or fraction-field property is used
in these definitions or proofs. For the intended O-module application
these data are specialized to the integer ring, fraction field and
uniformizer. F and R share a universe; O may have a different universe.
The source and target have fixed global coordinates.

This construction does not identify `LocalQuasiIsogeny` with the earlier
invertible-tensor `QuasiIsogeny`, construct composition or inverses of
arbitrary sheaf sections, assign rational heights, or prove nilpotent
rigidity. It does not assert representability.
