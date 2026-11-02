# Rank one reflected from a local residue fibre

`nonempty_linearEquiv_of_flatLocalBaseChange` proves that for a flat local
map of commutative local rings `A → B` and a finite `A`-module `M`,
an equivalence `B ⊗[A] M ≃ₗ[B] B` implies an equivalence `M ≃ₗ[A] A`.
A flat local map is faithfully flat, so flatness descends from the
trivialized base change. Finite flat modules over the local ring `A`
are free, and free-module finrank is unchanged by extension of scalars.
The equivalence over `B` gives finrank one and hence the desired
equivalence over `A`. `linearEquivOfFlatLocalBaseChange` chooses it.
This result uses only finiteness of `M`, and has three independent
ambient universes.

For a local map of commutative local rings `R → A`, an essentially finitely
presented `R`-algebra `A`, and an `A`-module `M` which is finitely presented
over `A` and flat over `R`, `nonempty_linearEquiv_of_residueFiber` proves
that `M` is isomorphic to the regular `A`-module if its actual residue
fibre is isomorphic to the regular fibre ring.
The fibre ring is `F = A ⊗[R] IsLocalRing.ResidueField R`; the fibre
module is `F ⊗[A] M`. The result has three independent ambient universes
and makes no noetherian assumption.

This is an internal derived result. Its inputs are the published
`Langlands.Algebra.essFinitePresentationFiberwiseFlatness`
(Stacks Project tag 00R7), the published local residue-fibre ring
construction, and Mathlib's local finite-flat freeness and free-module
dimension results. The proof first obtains nontriviality of `M` from
the fibre isomorphism and nontriviality of the local fibre ring. The
fibre isomorphism gives fibre flatness; the fibrewise flatness criterion
with its two upper rings both equal to `A` then gives `A`-flatness.
Finite flat modules over a local ring are free. Base change preserves
the finrank of a free module, so the fibre isomorphism makes that
finrank one. The free rank-one classification supplies the desired
linear equivalence.

`linearEquivOfResidueFiber` chooses one such actual `A`-linear
equivalence `M ≃ₗ[A] A`. The choice is noncomputable; it is not
asserted to reduce to the supplied fibre equivalence.

`linearEquivOfResidueFiberBaseChange` combines the two constructions:
it suffices to trivialize the actual residue-fibre module after a flat
local extension `F → B` to another commutative local ring. It first
descends rank one to `F` and then reflects it to `A`. This version has
four independent ambient universes. It assumes flatness and locality
of the fibre extension explicitly; it does not construct those
properties for a geometric base change.

This algebraic lemma does not assert an identification of sheaf
pullback stalks with tensor products, spreading a stalk basis to an
open neighbourhood, the base-change criterion for a line-bundle locus,
or any stack atlas.
