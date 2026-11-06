# Normal-subgroup simple connectedness from semisimple complements

This internal adapter works over every field `k : Type u`, with arbitrary
universe `u`. It retains
`SemisimpleNormalIsogenyComplementStatement.{u}` as an explicit hypothesis.

Given a simply connected group scheme `G`, a closed subgroup homomorphism
`j : H ⟶ G`, smoothness and connectedness of `H`, and normality of the full
all-test range of `j`,
`IsSimplyConnected.normalSubgroup_of_normalIsogenyComplement` proves
`IsSimplyConnected H`. No almost-simple hypothesis on `H` is required.

The construction
`IsSimplyConnected.normalFactorCoverIso_of_normalIsogenyComplement`
also takes a semisimple group scheme `C` and a central isogeny `f : C ⟶ H`.
It returns an actual group-scheme isomorphism `C ≅ H`. The companion
`_hom` lemma says that its forward morphism is the original `f`.

The proof applies the supplied complement assertion to the prescribed `j`.
It obtains semisimple `H` and `K`, a semisimple product `H ⊗ K`, all-test
commutation, and a central-isogeny multiplication `m : H ⊗ K ⟶ G`.
Simple connectedness of `G` makes `m` an isomorphism. Transport through
`asIso m` makes the product simply connected, and
`IsSimplyConnected.of_tensor_left` gives simple connectedness of `H`.
Its defining central-isogeny criterion then makes `f` an isomorphism;
`asIso f` supplies the constructed isomorphism and the forward-map identity.

This is a composition of the Library's simple-connectedness definition and
the direct-factor helper. It extracts the normal-factor step also used in
the conditional rational-generation induction by Workers 1371 and 1636,
so consumers can use it without importing that induction. It supplies
neither a proof of the complement assertion nor the unconditional
rational-generation theorem. Those structural and final proof obligations
remain open.
