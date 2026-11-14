# Local representatives for a group-valued right coset

This internal construction descends a group point modulo a supplied subgroup.
It is a supporting step for local conjugacy; it does not assert the existence
of a Borel subgroup, a vector series, or a cover with conjugating points.

`HasLocalCosetRepresentatives i g` says that at each base point there is an
open neighbourhood `W`, a point `s` of the ambient group over `W`, and a point
`f` of the subgroup over the restricted cover, such that `g f = s` after
restriction and pullback. All factors are actual morphisms over the original
base. In particular, this definition requires a simultaneous factorization on
the restricted cover, not just membership of individual geometric points in
the same coset.

`LocalCosetDescent.hasLocalCosetRepresentatives` assumes a monomorphic
subgroup map and a quasi-compact, flat, surjective cover. Its point `g` has a
subgroup-valued difference cocycle: every value of the coboundary of `g⁻¹`
lifts through the subgroup. If that lifted cocycle is Zariski locally
trivial, the theorem supplies the local representatives.

The proof chooses a local trivializing cochain `f`. The coboundary identity
and the subgroup inclusion give
`g(a)⁻¹ g(b) = f(a) f(b)⁻¹` on every pair of test points of the restricted
cover. Consequently `g f` has equal pullbacks on every such pair. The
restricted cover remains quasi-compact, flat and surjective, so its
effective epimorphism descends `g f` to a scheme morphism over `W`.
Cancellation of the cover shows that this morphism has the correct
structure map to the original base, yielding the required factorization.
No commutativity or normality of the subgroup is assumed.

`LocalCosetDescent.hasLocalCosetRepresentatives_of_vectorSeries` supplies
the local cocycle hypothesis from `SplitSolvableLocalCocycle`: over `Spec R`,
the subgroup and its split-torus quotient are affine, the quotient map is
flat, surjective and locally finitely presented, and its full scheme kernel
is the image of an affine group with a supplied finite vector series. The
cover is affine, flat and surjective. The result permits every commutative
ring, arbitrary universes, disconnected bases and the empty spectrum.

The construction generalizes the right correction in
`Torus.FieldTransporterDescent` to arbitrary subgroup schemes and local
trivializations, and uses the same scheme descent mechanism as
`Torus.OpenSections`. It is derived from the actual cocycle lifting and
local trivialization APIs and Mathlib's fpqc effective epimorphism theorem.
