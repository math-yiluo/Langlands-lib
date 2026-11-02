# Relative finite projective space

`RelativeProjectiveSpace S n` constructs projective `n`-space over any scheme
`S : Scheme.{u}` as the pullback of the existing integral polynomial-Proj
model `ProjectiveSpace (ULift.{u} ℤ) n` along the unique map from `S` to the
terminal scheme. There is no finiteness, noetherianity or nonemptiness
assumption on `S`, and `n` may be zero.

The source is Stacks Project Section 27.13, Definition 27.13.2 and its
following paragraph, in the registered original
`stacks-projective-space-twists-morphisms-2026-10-26`, local file
`literature/Stacks Project - Projective space, twists and projective morphisms (HTML snapshot 2026-10-26)/01ND.html`.
Stacks defines the relative space by base change of the integer model.
The Lean construction uses the chosen terminal scheme in the same universe;
Mathlib's `specULiftZIsTerminal` identifies the lifted integer spectrum as
terminal. Uniqueness of maps to a terminal object supplies the pullback
compatibility. The integral model is the actual Proj of the polynomial ring
on `Fin (n + 1)` with its total-degree grading, imported without alteration.

`toBase` and `toIntegral` are the two scheme projections. `lift n p q` is the
unique map determined by a scheme morphism `p : X ⟶ S` and a scheme morphism
`q` to the integral model. The two projection formulas, `hom_ext` and
`lift_projections` are proved from the pullback universal property.
`homEquiv` packages that property as an equivalence between the actual Hom
type into relative projective space and the product of these two Hom types.
This is the map description in the paragraph following Definition 27.13.2.

`map n f` is the induced map for every scheme morphism `f : S ⟶ T`, retaining
the integral projection and composing the base projection with `f`.
The two projection identities prove its identity and composition laws by
Hom extensionality. `functor n` packages those maps as a functor on schemes.

`baseChangeIso n f` is an actual scheme isomorphism from relative projective
space over `S` to the pullback of relative projective space over `T` along
`f`. Its forward map is the pullback lift of `toBase S n` and `map n f`;
its inverse lifts the changed-base projection and the composite integral
projection. The inverse identities follow from Hom extensionality and
the pullback square's commutativity. Four projection formulas identify
these maps, and `isPullback_map` records the resulting Cartesian square.
These categorical verifications are internal consequences of the
source-backed construction, implemented with Mathlib's scheme limits.

This module does not compare its scheme with `ProjectiveSpace R n` for a
general ring `R`, construct a projective bundle of a nontrivial locally free
sheaf, or prove a cubic embedding, a quotient or moduli representability.
Those are separate obligations.
