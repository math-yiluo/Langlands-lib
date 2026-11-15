# Split subtori of full split rank are maximal split tori

Worker 224. This is an internal derivation from published Library results. It is a helper for the
proof of `Langlands.Geometry.Building.SpecialTorusExistenceStatement` (Kaletha–Prasad,
Proposition 9.3.4) and makes no independent literature assertion.

Let `k` be a field, `G` a group scheme over `Spec k` and `i : T ⟶ G` a closed split subtorus
(`IsSplitSubtorus i`), with a chosen isomorphism `e : T ≅ splitTorus J` for a finite type `J`.

`IsSplitSubtorus.isMaximalSplitTorus_of_splitRank_le` proves that `i` is a maximal split torus
(`IsMaximalSplitTorus i`) when `splitRank G ≤ Nat.card J`. Take a split subtorus
`i' : T' ⟶ G` with an isomorphism `e' : T' ≅ splitTorus J'` and a factorization
`f ≫ i' = i`. Since `i` is a closed immersion, the composite `f ≫ i'` is a monomorphism, hence
so is `f`, and so is `g := e⁻¹ ≫ f ≫ e'`. The Library lemma `splitTorus.card_le_card_of_mono` gives
`Nat.card J ≤ Nat.card J'`, while `IsSplitSubtorus.card_le_splitRank` and the hypothesis give
`Nat.card J' ≤ splitRank G ≤ Nat.card J`. So the two cardinals are equal, and
`splitTorus.isIso_of_mono_of_card_eq` makes `g`, hence `f = e ≫ g ≫ e'⁻¹`, an isomorphism.

`IsSplitSubtorus.isMaximalSplitTorus_of_card_le` is the form used downstream. It assumes that every
maximal split torus of `G`, with any chosen splitting `A ≅ splitTorus I`, has `Nat.card I` equal
to `splitRank G`. It also takes one maximal split torus `a : A ⟶ G` with
`A ≅ splitTorus I` and `Nat.card I ≤ Nat.card J`. Then the rank hypothesis turns this inequality
into `splitRank G ≤ Nat.card J`, and the first theorem applies. For a connected reductive group
the rank assumption is part 2 of the Library's `maximalSplitTorusConjugacy`.
