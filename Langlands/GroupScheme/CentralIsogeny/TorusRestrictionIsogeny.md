# Torus restrictions of central isogenies from maximal split images

Author: Worker 1375.

This is an internal conditional construction for the exact central-isogeny
root-datum task. It uses
`CentralSurjectionMaximalSplitTorusImageStatement` as an explicit premise.
It does not prove that geometric statement.

Over any field `k : Type u`, let `G` and `G'` be connected reductive groups,
let `i : T → G` and `i' : T' → G'` be split maximal tori, and let
`φ : G → G'` be a central isogeny. Consider any actual homomorphism
`t : T → T'` with `i ≫ φ = groupHom t ≫ i'`.

`IsCentralIsogeny.isIsogeny_torusRestriction_of_maximalImage` proves that
`groupHom t` is finite, flat and surjective. It first applies
`IsSplitTorus.fppfImage` to `t` itself. Write the resulting actual
factorization as `T → E → T'`. The projection is fppf, and `E → T'` is a
closed split subtorus. Composing that inclusion with `i'` gives a closed
split subtorus of `G'` and a factorization of `i ≫ φ`.

Apply the supplied maximal-image theorem to the central fppf map `φ` and
this factorization. The image `E → G'` is maximal split. It factors through
the split torus `T' → G'`, so maximality makes `E → T'` an isomorphism.
Composing the fppf projection `T → E` with that isomorphism makes `t` flat
and surjective. Finiteness follows independently from the commuting square,
the two closed embeddings and finiteness of `φ`, using the published
`isFinite_torusRestriction`.

`IsCentralIsogeny.characterPullback_injective_of_maximalImage` then makes
the actual integral character pullback `χ ↦ t ≫ χ` injective. A flat
surjective scheme morphism is epimorphic, and the published character
restriction lemma cancels it on actual character morphisms. It assumes
no surjectivity on rational points.

`TorusRestrictionQuasiInverse t` records an integer `n ≠ 0`, an actual
reverse torus morphism `g : T' → T`, and the two equations
`t ≫ g = n • identity` and `g ≫ t = n • identity`.
`IsCentralIsogeny.torusRestrictionQuasiInverseOfMaximalImage` constructs
these data by the preceding isogeny theorem and the published
`IsSplitTorus.exists_isogeny_quasiInverse`. The integer remains nonzero
even if the field has positive characteristic; it is an integer in the
Hom-group structure, with no cancellation in the base field.

The proof adds no characteristic, perfection, separability or smooth-kernel
assumption. The geometric maximal-image premise remains essential and
must be discharged by its independent proof before using this unit in
the unconditional host theorem.
