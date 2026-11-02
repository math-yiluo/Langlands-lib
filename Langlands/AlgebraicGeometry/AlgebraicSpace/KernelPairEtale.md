# Étaleness of a quotient map from its kernel pair

Authors: Worker 1001.

Internal infrastructure for the proof of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement`.
This module implements the argument of the proof of Lemma 65.10.3
(Tag [02WV](https://stacks.math.columbia.edu/tag/02WV), retained as
`stacks-etale-quotient-effective-fppf-descent-2026-11-01`) for étaleness, in a general form.
It applies to any presheaf with representable diagonal that receives a locally surjective
map from a scheme whose kernel pair is represented. The declaration is in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPair`.

## Statement

`isEtale_of_isPullback a hdiag h hs`: let `Q` be a presheaf on `Over S` and let
`a : (schemeYoneda S).obj U ⟶ Q` be fppf locally surjective. Let `t s : R ⟶ U` satisfy
`h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a`. If `Q` has
representable diagonal (`hdiag`) and `s.left` is étale (`hs`), then `IsEtale a`, in the
sense of `AlgebraicSpace.Basic`. That is, `a` is representable and every base change of `a`
along a map from a scheme is étale on underlying schemes.

## Proof

Representability of `a` follows from the representable diagonal
(`Functor.relativelyRepresentable.of_diag`). By `MorphismProperty.relative_of_snd` it
remains to show that, for every `T : Over S` and `g : (schemeYoneda S).obj T ⟶ Q`, the chosen
projection `(hr.snd g).left` of the represented base change is étale.

Because `a` is locally surjective, the section of `Q` corresponding to `g` lifts to `U` on an
fppf covering sieve of `T` (`Presheaf.imageSieve_mem`). By
`GrothendieckTopology.mem_over_iff` this sieve gives a covering sieve of the scheme `T.left`
for `Scheme.fppfTopology`. By `FppfLocal.of_fppfTopology_sieve` for `@Etale`, it suffices
to treat a member `f : Y ⟶ T.left` of that sieve. For such `f` there is a lift
`τ : T' ⟶ U` with `T' = Over.mk (f ≫ T.hom)`, so that `(schemeYoneda S).map τ ≫ a` equals
`(schemeYoneda S).map f' ≫ g` for `f' = Over.homMk f`
(`map_comp_eq_map_comp_of_app_eq`, `schemeYoneda_app_up`).

Let `W` be the pullback of `s` and `τ` in `Over S`. Pasting its square with the kernel pair
square `h` shows that `W` represents the base change of `a` along
`(schemeYoneda S).map f' ≫ g`. Cancelling the pullback square of `hr` (`IsPullback.of_right`)
shows that `W ⟶ T'` is the base change of `hr.snd g` along `f'`. The comparison map comes
from a morphism of schemes because `schemeYoneda S` is full, and the square is a pullback of
schemes over `S` (`isPullback_of_map`) and hence of underlying schemes. Finally
`(pullback.snd s τ).left` is étale as a base change of the étale `s.left`. This matches the
source's identification `T_i ×_T (T ×_{U/R} U) = T_i ×_{a_i, U, t} R`, with the roles of the
two projections exchanged.

The proof needs `set_option backward.isDefEq.respectTransparency.types false` so that the
Mathlib fppf descent instance for `@Etale` is found. It also states explicitly that `@Etale`
is Zariski local on the target (`HasRingHomProperty.instIsZariskiLocalAtTarget`).
