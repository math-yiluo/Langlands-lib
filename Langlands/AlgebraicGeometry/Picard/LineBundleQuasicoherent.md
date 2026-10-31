# Quasi-coherence of actual locally free rank-one sheaves

In any universe `u`, an actual scheme-module sheaf `M` satisfying the
published `IsLocallyFreeRankOne M` condition is quasi-coherent in
Mathlib's sense. The condition supplies an open neighborhood of every
point on which the actual restriction of `M` is isomorphic to the
structure sheaf. The result adds no finiteness condition on the scheme
and no affine, separated, reduced, or noetherian hypothesis.

`IsLocallyFreeRankOne.isQuasicoherent` chooses those neighborhoods and
uses them as a cover indexed by the points of the scheme. On each open,
the published `Langlands.Scheme.Modules.unitLocalBasis` transports the
actual trivialization to an isomorphism from the free sheaf on the
one-element type to `M.over U`. The free sheaf is quasi-coherent, and
quasi-coherence is invariant under isomorphisms. Mathlib's
`SheafOfModules.IsQuasicoherent.of_coversTop` glues these local
quasi-coherence assertions to `M`.

`LineBundle.isQuasicoherent` records the result as an instance for the
underlying module sheaf of a `LineBundle`.
`LineBundle.toQuasicoherent` lifts the underlying module sheaf functor
to the full subcategory of quasi-coherent sheaves. It sends each actual
line bundle to its underlying sheaf with the quasi-coherence proof above,
and each morphism to the same underlying module-sheaf morphism.
`LineBundle.toQuasicoherentCompForgetIso` identifies its composite with
the inclusion into module sheaves with `LineBundle.forget`; the
isomorphism is the identity.

The explicit lemma
`IsLocallyFreeRankOne.isQuasicoherent_pullback` uses the published
preservation of local rank one under pullback and applies the first
lemma. It holds for every scheme morphism and concerns the actual
`Scheme.Modules.pullback` functor.

This pair is an internal consequence of the published local rank-one
and local-basis constructions and Mathlib's definition of
quasi-coherence. It does not assert preservation of arbitrary
quasi-coherent sheaves by pullback, a cohomology base-change theorem,
or the relative cube theorem.
