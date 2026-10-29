# Epimorphisms between actual multiplication kernels

This internal construction identifies actual multiplication kernels with
pullbacks and proves the resulting epimorphism consequences. It supplies a
prerequisite for the relative finite Weil alternation assembly. The
multiplication-isogeny statement and the final alternation statement remain
separate proof obligations.

For a commutative group object `G` over any scheme `S` and `n ∣ m`, the actual
transition `G[m] → G[n]` fits in a pullback square whose top and bottom maps
are the inclusions `G[m] → G` and `G[n] → G`, and whose right map is
multiplication by `m / n`. The proof uses the published kernel pullback
squares and multiplication composition. Pasting with the kernel square for
`n` yields the kernel square for `m`; pullback cancellation establishes the
transition square.

`Langlands.GroupScheme.Tate.kernelTransitionPullbackIso` is the resulting
canonical isomorphism in `Over S` from the actual kernel `G[m]` to the
pullback of `[m / n] : G → G` along the inclusion `G[n] → G`.
Its two projection lemmas identify its composites with the pullback
projections as the actual inclusion `G[m] → G` and the actual transition
`G[m] → G[n]`, respectively. It is constructed from the proved pullback
square by the universal property. Forgetting from `Over S` also gives a
pullback square of schemes.

Flatness and surjectivity of multiplication by `m / n` therefore pass to
the transition by base change. Mathlib's theorem
`AlgebraicGeometry.Flat.epi_of_flat_of_surjective` then makes the underlying
scheme map an epimorphism. The forgetful functor from `Over S` reflects
epimorphisms, giving the slice-category conclusion.

For an actual abelian scheme `A/S` and `n > 0`, the specialization `m = 2 * n`
has quotient `m / n = 2`. Assuming exactly
`Langlands.GroupScheme.MultiplicationIsogenyStatement` supplies the flatness
and surjectivity of `[2]` from the smooth, proper and geometrically connected
structure of `A`. The final lemma is
`Langlands.AbelianScheme.kernelDoubling_epi_of_multiplicationIsogeny`,
with arguments `(hIsogeny) (S) (A) (n) (hn : 0 < n)` and conclusion
`Epi (Tate.kernelTransition A.toGrp (dvd_mul_left n 2))` in `Over S`.
The preceding lemma gives epimorphy of its underlying scheme map.

This is an internal consequence of the published kernel and multiplication
constructions and Mathlib's pullback and faithfully flat epimorphism
results. It introduces no new literature assertion. All squares and
cancellation arguments concern actual scheme morphisms; no reduction to
geometric points or invertibility assumption on the torsion order is used.
The multiplication-isogeny hypothesis remains an outstanding proof
dependency.
