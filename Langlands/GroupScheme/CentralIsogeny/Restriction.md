# Finite fppf restrictions to commutative closed subgroups

Author: Worker 1469.

This is an internal supporting module for the proof of
`SimplyConnectedCoverSplitTorusStatement`. It is a formal consequence of the
published closed-subgroup and central-isogeny predicates and Mathlib's
morphism-property results; it introduces no additional mathematical assumption.
Its lemmas work over any base scheme, without reductivity or a field hypothesis.

Suppose `π : C ⟶ G` is finite, `j : T ⟶ C` and `i : S ⟶ G` are closed
subgroup embeddings, and `f : T ⟶ S` is a homomorphism of commutative group
schemes satisfying `j ≫ π = groupHom f ≫ i`.

`isFinite_of_closed_subgroup_restriction` proves that `f` is finite. A
closed immersion is finite, so `j ≫ π` is finite. The square identifies
this composite with `f ≫ i`. The closed immersion `i` is separated, so
Mathlib's `AlgebraicGeometry.IsFinite.of_comp` gives finiteness of `f`.

`isCentralIsogeny_of_fppf_closed_subgroup_restriction` additionally takes
flatness, surjectivity, and local finite presentation of the underlying
scheme morphism of `f`. It combines these with the preceding finiteness
lemma to supply the morphism-property fields of `IsCentralIsogeny`.
Its remaining field concerns the actual scheme-theoretic kernel inclusion.
Every kernel point commutes with every point of `T` after every restriction
because `T` is commutative; `Commute.all` proves this field directly.

The proof neither replaces the kernel by its rational points nor assumes
surjectivity on rational points. No assertion about lifting maximal split
tori is proved here. That separate existence theorem must supply the
commuting square and the three fppf properties in the eventual application.
