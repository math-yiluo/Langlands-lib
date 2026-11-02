# Closed immersions of etale field schemes into locally Noetherian schemes

Author: Worker 509.

This internal derived lemma concerns actual schemes over an arbitrary field
`k : Type u`. Let `i : Z → U` be an immersion and let `p : U → Spec k`.
Suppose that `U` is locally Noetherian and that `i ≫ p` is etale. Then `i`
is a closed immersion. Neither `U` nor `Z` is assumed quasi-compact.

For affine `U`, its locally Noetherian structure makes its topological space
Noetherian. The immersion is a topological embedding, so `Z` is Noetherian
as a topological space too. Consequently the morphism `Z → Spec k` is
quasi-compact. The published theorem
`GenericFiniteness.locallyQuasiFinite_of_formallyUnramified` makes the etale
structure morphism locally quasi-finite. Mathlib's
`IsFinite.of_locallyQuasiFinite` makes a quasi-compact locally quasi-finite
morphism to the Artinian scheme `Spec k` finite. The morphism `p` is
separated because both its source `U` and target `Spec k` are affine.
Thus `IsFinite.of_comp` makes `i` finite.
An immersion is a monomorphism, so the finite-monomorphism criterion gives
the desired closed immersion.

The general lemma checks closedness on the affine open cover of `U`.
The restricted source still has an etale morphism to `Spec k`: its map to
`Z` is the base change of the affine open immersion. The affine lemma
applies to each restricted square, and the Zariski locality of closed
immersions gives the conclusion.

The definition `etaleFieldImmersionComplement i p` packages the complement
of the set-theoretic image as an actual open subset of `U`. Its membership
lemma says exactly that a point lies in this open subset if and only if it
is outside the image of `i`. The closed-immersion lemma supplies the
openness proof.

This is a geometric input for a future Picard diagonal argument. It does
not construct an atlas or prove closedness of a sheaf diagonal by itself.
