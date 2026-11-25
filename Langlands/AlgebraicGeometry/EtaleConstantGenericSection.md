# Generic sections of étale locally constant parameters over a DVR

This is an internal derived geometric module. It combines the published
`EtaleGenericPullback`, `ConnectedCoproductFactorization`, and `SmoothReducedBase`
results with Mathlib's flat-base-change theorem for scheme-theoretic dominance,
separated-target equality theorem, and effective-epimorphism descent. The proof
route is described below; no external-source existence theorem is asserted.

## Parameters and conclusion

Let R be a commutative domain and a discrete valuation ring, and let K be a
specified fraction field with its original R-algebra structure. Let C be a scheme
over Spec R with separated structure morphism. Suppose q : U → Spec R is an
étale surjection, U is connected, I is any type in the scheme universe, and an
actual isomorphism over U identifies C pulled back to U with the coproduct of
I copies of U, whose structure map is the coproduct of identity morphisms.

`existsUnique_section_of_connected_etale_trivialization` proves that every
specified K-point p of C over Spec R extends to a unique section of C over
Spec R. Its restriction equality is equality of morphisms in the original
slice category, using the original `Spec.algebraMap R K`.
`sectionOfConnectedEtaleTrivialization` chooses that unique section as an actual
morphism in the slice category, and
`sectionOfConnectedEtaleTrivialization_generic` proves its exact restriction law.
The construction uses classical choice on the proved unique-existence theorem.

There is no assumption that I is finite or inhabited, that U is quasi-compact,
or that R is henselian or complete. The empty index case cannot admit such a
generic point under these hypotheses.

## Implemented proof

`isDominant_genericPullbackFst` first proves that base change of the specified
fraction-field map along any flat scheme over the domain R is dominant.
The fraction-field map is dominant by `isDominant_fractionFieldMap`; its target
is reduced, so it is scheme-theoretically dominant. It is an affine, hence
quasi-compact, morphism. Mathlib preserves scheme-theoretic dominance under
flat base change, and the resulting quasi-compact map is dominant.
This lemma only needs a domain R, not the discrete valuation hypothesis.

`exists_section_on_connected_etale_trivialization` constructs a section over U.
The published `connectedSpace_etale_genericPullback` makes U × Spec K connected.
The given generic point induces a morphism from that pullback to the
trivializing coproduct. The published connected-source factorization theorem
factors it through one summand. Because the morphism is over U, its factor to
that summand is exactly the projection to U. The chosen summand's identity
section, transported back through the specified isomorphism, gives a map
U → C with its required base equation and exact generic restriction. This
local construction does not require separatedness of C or surjectivity of q.

For the main theorem, the two induced maps U × Spec R U → C agree generically
by the local restriction equation. Their source is étale, hence smooth, over
the reduced spectrum of R, so it is reduced by `SmoothReducedBase`.
The generic pullback projection is dominant by the first lemma. Mathlib's
`ext_of_isDominant_of_isSeparated` therefore proves equality of the two maps.
The étale surjection q is an effective epimorphism of schemes; the regular
epimorphism universal property of its kernel pair descends the map U → C to
Spec R → C. Epimorphic cancellation proves its equation over Spec R. Base
change of q to Spec K is again an étale surjection and an epimorphism, so its
cancellation proves that the descended section restricts to the original p.
Finally, the same separated-target equality theorem on the reduced base
Spec R and its dominant fraction-field map proves uniqueness.

This module assumes a supplied connected étale trivialization. It does not
construct a trivialization for outer-isomorphism schemes or a finite
outer-class carrier; those are separate inputs and consequences.
