# Base change of full-product factorization

Worker 445. This is internal categorical infrastructure for the universal
closed-factorization locus. It derives its constructions from Mathlib's chosen
pullbacks, the adjunction `Over.mapPullbackAdj`, and the monoidal structure on
`Over.pullback`; it does not assert an additional literature theorem.

For a morphism of schemes `f : S' ⟶ S`, `schemeProductIso` and `productIso`
identify `(X ×[S] S') ×[S'] T`, regarded over `S`, with `X ×[S] T`, where the
structure map of `T` over `S` is its structure map over `S'` followed by `f`.
The forward map has components the composite of the two first projections and
the second projection. The inverse first lifts into `X ×[S] S'` and then into
the iterated pullback. The proofs of the inverse identities use pullback
extensionality. `productIso_hom_fst` and `productIso_hom_snd` give its components.

For `d : D ⟶ X ⊗ Y` in `Over S`, `baseChangedMap f d` is the pullback of `d`
followed by the inverse tensor comparison of the monoidal pullback functor.
Its codomain is therefore the actual product of the two base-changed factors.
The accompanying instance proves that its underlying scheme morphism is a
closed immersion whenever the underlying morphism of `d` is a closed immersion:
pullback preserves this property and the tensor comparison is an isomorphism.

`originalMap f t` sends a morphism `T ⟶ (Over.pullback f).obj Y` to the
corresponding morphism `(Over.map f).obj T ⟶ Y` under the adjunction. Its
underlying map is `t.left` followed by the first pullback projection.
`originalMap_comp` records compatibility with composition by a pulled-back
morphism. `tensorComparison_fst`, `tensorComparison_snd`, and
`originalMap_whisker` compare the product map specified by a test before and
after forgetting the changed base; their proofs check the two projections.

Finally, `factors_iff` proves, for every `T : Over S'` and
`t : T ⟶ (Over.pullback f).obj Y`, that there is a factorization

`q ≫ baseChangedMap f d = ((Over.pullback f).obj X ◁ t)`

if and only if there is a factorization

`q₀ ≫ d = (X ◁ originalMap f t)`.

The forward direction composes with the tensor comparison, applies the
adjunction, and precomposes with `productIso.inv`. The reverse direction applies
the adjunction to `productIso.hom ≫ q₀` and uses injectivity of the adjunction
equivalence to recover the required equality. Cancelling the tensor comparison
then yields the base-changed factorization.

All schemes are in arbitrary universe `u`. No affineness, flatness, finiteness,
or representability assumption is needed for the comparison. In particular,
`factors_iff` also works for a nonmonomorphic `d`. This supporting module does
not construct the closed-factorization locus itself.
