# Transitivity on the geometric fibre of a connected finite étale cover

The module `Langlands.AlgebraicGeometry.FiniteEtale.ConnectedCoverFiber`
proves that the pointed finite étale fundamental group acts transitively on
the geometric fibre of a finite étale cover whose total space is connected.
This is the property of Galois categories that the automorphism group of a
fibre functor acts transitively on the fibre of a connected object, applied to
the Library's fibre functor at an actual geometric point.

## Declarations

Let `S` be a scheme, `Ω` an algebraically closed field and
`s : Spec Ω ⟶ S` a geometric point with finite geometric fibres `hs`.

- `surjective_fiber_of_surjective`: if `i : Z ⟶ Y` is a map in `Cover S` whose
  underlying morphism of schemes is surjective, then composition with `i`
  maps `Fiber s Z` onto `Fiber s Y`.
- `exists_smul_eq_of_connectedSpace`: if `S` is connected and locally
  Noetherian and the total space of `Y : Cover S` is connected, then for all
  `p p' : Fiber s Y` there is `σ : FundamentalGroup s hs` with `σ • p = p'`.

## Proofs

`surjective_fiber_of_surjective`: `i` is finite and étale, since its
composite with the structure map of `Y` is the structure map of `Z`, and both
structure maps are finite étale (Mathlib's `IsFinite.of_comp` and
`Etale.of_comp`). The pinned `weil-conjectures` package lemma
`Scheme.Hom.exists_lift_of_isSepClosed` lifts a point `Spec Ω ⟶ Y` along a
finite étale morphism whose image contains the image of the point, because
`Ω` is separably closed; surjectivity of `i` provides this. The lift is a
point of `Fiber s Z` mapping to the given point.

`exists_smul_eq_of_connectedSpace`: the Library theorem
`geometricGaloisFiberFunctor` makes `Cover S` a Galois category with fibre
functor `F = fiberFunctor s hs`. It suffices to show that `Y` is a connected
object; then Mathlib's
`PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected` gives
transitivity. `Y` is not initial, because its fibre contains `p`. Let
`i : Z ⟶ Y` be a monomorphism from a non-initial `Z`. Its underlying
morphism is finite and étale, so its image is closed and open. The image is
nonempty because the fibre of `Z` is nonempty. Since `Y` is connected, `i` is
surjective, so it is surjective on fibres by the first lemma. If `i` were not
an isomorphism, Mathlib's `PreGaloisCategory.lt_card_fiber_of_mono_of_notIso`
would make the fibre of `Z` strictly smaller than that of `Y`, which
contradicts surjectivity.
