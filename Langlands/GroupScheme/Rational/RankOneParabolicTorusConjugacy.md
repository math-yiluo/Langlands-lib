# Split tori in a rank-one parabolic with descended conjugation

This internal unit proves local conjugacy for actual maximal split tori in an
actual dynamic parabolic. It works over every field `k : Type u`. Let
`i : T.toGrp → G` be a maximal split torus, let `a` be a nonzero character of
`T`, and suppose an actual automorphic action `e` of the multiplicative group
on `G` restricts along `a` to conjugation by `i`. Let `ν` pair positively with
`a`, and write `χ = ν ≫ i` and `U = Dynamic.unipotent χ`.

The main result
`RelativeRoot.exists_unipotent_conjugacy_of_range_le_parabolic_descendedAction`
assumes that `G` is smooth and affine and that an ambient maximal split torus
`s : D.toGrp → G` has its whole subgroup-functor range contained in
`Dynamic.parabolic χ`. It constructs a rational point `u` of the actual
subgroup `U` and an isomorphism `f : D.toGrp → T.toGrp` such that
`(f ≫ i) ≫ (G.innerIso u).hom = s`. The containment is tested on every scheme,
and the conclusion is equality of group-scheme morphisms. There is no
perfectness, characteristic, connectedness or reductivity hypothesis on `G`.
The descended-action assumption is essential to this particular local result.

`Dynamic.parabolicLimitHomOfRange` is the actual ambient limit homomorphism
used in this construction. Over any scheme `S`, for a group scheme `G`
separated over `S`, a cocharacter `χ`, chosen representatives
`iP : P → G` and `iZ : Z → G` of its dynamic parabolic and centralizer,
and a group-scheme map `s : D → G` whose range lies in the parabolic,
it is the composite
`hP.factorHom s hsP ≫ Dynamic.limitGroupHom hP hZ ≫ iZ`.
Thus its value on any test point is the actual limit at zero of the image
under `s`. This definition does not require a field or a torus source.

Two preparatory results record parts of the construction.
`RelativeRoot.exists_limit_factor_of_range_le_parabolic_descendedAction`
requires only affineness of `G` and splitness of `D`. It constructs a map
`f : D.toGrp → T.toGrp` for which
`s(x) * i(f(x))⁻¹` lies in `U` on every scheme test.
`RelativeRoot.limit_factor_character_ne_zero_of_descendedAction` assumes
smoothness of `G`, ambient maximality of `s`, and this displayed all-test
condition for a supplied `f`. It proves `f ≫ a ≠ 0`. This second result does
not require the positive-pairing hypothesis on `ν`.

## Implemented proof

Factor `s` through the canonical affine representative of the dynamic parabolic.
The exported `Dynamic.parabolicLimitHomOfRange` applies its actual limit
homomorphism to the canonical dynamic centralizer and composes with that
centralizer's inclusion into `G`. The descended-action
centralizer comparison identifies this dynamic centralizer with the centralizer
of the whole torus `T`. The limit map therefore commutes with `i` on every
test. The existing commuting split-torus factorization theorem for a maximal
split torus constructs `f`. The formula for the limit homomorphism and
`Dynamic.mul_inv_limit_mem_unipotent` give the asserted difference condition.

If `f ≫ a` vanished, the character-kernel centrality theorem in
`SplitTorusCentralDifference` would make `f ≫ i` central. The canonical affine
representative of `U` is unipotent: the proof applies the existing dynamic
unipotence theorem to the unconditional `torusActionUnipotence` proof.
The split-torus central-difference vanishing theorem then gives `s = f ≫ i`.
Ambient maximality of `s` makes `f` invertible, contradicting `a ≠ 0`.

Choose a cocharacter `ζ` of `D` pairing positively with the nonzero character
`f ≫ a`, and set `ν₂ = ζ ≫ f`. The descended-action comparisons identify
`U_G(ν₂ ≫ i)` with `U` and identify `Z_G(ν₂ ≫ i)` with the centralizer of
`T`. Evaluate the difference condition at the universal `ζ`-point.
`Dynamic.exists_unipotent_conj_of_mul_inv_mem` supplies a rational point
`u ∈ U` conjugating `ν₂ ≫ i` to `ζ ≫ s`. Conjugating the whole map `s` back
by the inverse inner automorphism gives a torus whose image centralizes
`ν₂ ≫ i`, since a commutative group's points centralize its cocharacters.
It consequently centralizes all of `T`, so the same commuting factorization
argument factors this conjugate through `i`. Maximality makes the resulting
factor an isomorphism. Compose back with the inner automorphism to obtain
the displayed equality.

## Provenance and scope

This is a derived internal argument from the existing affine dynamic
representatives, limit homomorphism, descended-action comparisons, commuting
split-torus factorization, split-torus-to-unipotent vanishing and cocharacter
cocycle conjugacy. It is not a translation of an additional literature result.
The only facts used from `RootFactorPairExistenceReduction` are its
`dynamicUnipotent_eq_subgroup_of_descendedAction` and
`dynamicCentralizer_eq_torusCentralizer_of_descendedAction`. That imported
module also contains a separate conditional general-Bruhat reduction; none
of the proofs in this unit calls that reduction or assumes a general Bruhat
or Tits-system statement.

This unit proves the stated local conjugacy. It does not construct a proper
flag quotient, a nontrivial Weyl element, rank-one two-cell covering or
opposite factor pairs, and it does not prove the host task's
`RootRankOneFactorizationStatement`.
