# Étale descent of the torus isomorphism locus

Let `i : H ⟶ G` be an actual group-scheme homomorphism over an arbitrary
scheme `S`. This module proves that the open immersion of
`TorusIsomorphismLocus.opens i` represents the condition that the actual
base change of `i` is an isomorphism, provided `H` is a
`RelativeTorus.IsTorus` and `G` is a split torus. Every test morphism
`b : T ⟶ S` is allowed, including those from nonreduced or disconnected
schemes. All schemes and residue fields lie in an arbitrary universe `u`.

`isIso_of_fppf_baseChange` first proves reflection of invertibility for
arbitrary actual group homomorphisms after a surjective flat locally
finitely presented base change. It applies Mathlib's descent of scheme
isomorphisms to `underlying_isPullback`, using the base-changed map of
the target group scheme as the covering map, and then reflects the
underlying isomorphism into actual group objects. Quasi-compactness of
the base-change map is not required: Mathlib derives this descent
property from fpqc descent and target locality of scheme isomorphisms.

For an étale map `q`, `etaleImage q` is the open subset with underlying
set `Set.range q`. The map is open because it is flat and locally
finitely presented. `isIso_etaleImage` factors `q` through this open
image. Its first factor is surjective, and it is étale by cancellation
against the open immersion of the image. The canonical comparison
between direct and iterated group-scheme base changes transfers the
given isomorphism to this surjective étale factor. The reflection
lemma then gives invertibility over the open image itself.
Consequently `etaleImage_le_opens` places this image in the union
`opens i`. These three facts do not require torus hypotheses.

`isIso_baseChange_iff_range_subset_opens_of_cover` assumes a common
jointly surjective étale cover of `S` on whose every member both
`H` and `G` become split tori. Suppose `i` becomes invertible along
an arbitrary test morphism `b`. For each point `t` of `T`, choose
a point `y` above it in the pulled-back splitting cover. The
residue-field map of `y` determines a field-valued point of the
corresponding cover member. The pullback equation and the direct
versus iterated base-change comparison show that `i` is invertible
at this field-valued point. The split-torus neighbourhood theorem
therefore supplies an open immersion into that cover member with
an exact factorization of the same field point and invertibility
on this neighbourhood.

The composite of this open immersion and the étale cover map is
étale. Its image contains `b(t)`, by the exact factorization and
the residue-field point formula, and lies in `opens i` by the
étale-image result. Thus the entire image of `b` lies in the open
union. The converse uses the already proved open-cover gluing
lemma `isIso_of_range_subset_opens` and needs no torus hypothesis.

`isIso_baseChange_iff_range_subset_opens_of_relative_split` applies
that criterion to the étale cover in `RelativeTorus.IsTorus H`;
the split target remains split on every cover member. Finally,
`isIso_baseChange_iff_factors_of_relative_split` uses the universal
property of the actual open immersion to express the criterion as
existence of `a : T ⟶ opens i` with `a ≫ (opens i).ι = b`.
Such a factor is unique because the open immersion is a monomorphism.

This is an internal derivation from the split-torus neighbourhood
construction, actual pullback comparisons, Mathlib descent, and the
published relative-torus definition. It introduces no new notion
of a torus and reuses published mathematics by Lean name. It proves
openness and the all-test factorization criterion, but does not
assert that this locus is closed, construct a universal Hom family,
or prove smooth Hom representability.
