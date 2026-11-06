# Proof: rank-one reductivity from an actual Weyl inversion

`rankOneWeylReductivity` proves the existing proposition
`RankOneWeylReductivityStatement.{u}` for an arbitrary universe `u`.
The hypotheses are unchanged. `G` is a smooth connected affine group
over an algebraically closed field `k` of any characteristic, and
`i : T → G` is an actual closed split torus. The existing all-test
centralizer of `i` is its own range. The actual nonzero adjoint weights
are exactly `α` and `-α`, with `α ≠ 0`, and both weight spaces have
dimension one. Finally, `c` is an automorphism of `T` with
`α ∘ c = -α`, and `n` is a `k`-point of `G` satisfying the
all-refinement transporter relation `i(c(t)) n = n i(t)`.

The main step, `RankOneWeylCriterion.hasTrivialUnipotentRadical`,
proves the existing ground-field radical predicate
`HasTrivialUnipotentRadical G` from these data. Together with the
smoothness, affineness and connectedness of `G`, this is
`IsPseudoReductive G`. The published algebraically closed comparison
`isConnectedReductive_of_isAlgClosed` then gives
`IsConnectedReductive G`.

## The radical argument

Let `j : H → G` be a smooth connected unipotent normal closed
subgroup. It suffices to show that `Lie(H)` is zero. The torus acts on
`H` by normalized conjugation, and `Lie(H)` is the internal direct sum
of the weight spaces of this action. The differential of `j` is
injective and carries each such weight space into the ambient weight
space with the same character. So it suffices to show that no weight
of `Lie(H)` has nonzero image.

For the zero weight the proof is the one in
`RankOneCentralizerDetection`. The published centralizing cocharacter
of `T` has all-test centralizer equal to the centralizer of `T`, which
by hypothesis is represented by `T` itself. Since `T` has trivial
unipotent radical, `normal_weight_zero_of_centralizer` kills the zero
weight. The same cocharacter and
`range_normalUnipotentCentralizer_eq_bot` also show that the
intersection of `H` with the range of `i` is the bottom subgroup.

A nonzero weight with nonzero image is an ambient root, so it is `α`
or `-α`. Call it `β`, and let `Y` be a nonzero element of
`Lie(H)` in its weight space. The rest of the proof derives a
contradiction in five steps.

1. **Both root lines lie in `Lie(H)`.** The weight space of `β` is
   one-dimensional and contains the nonzero element `Y` of the image of
   the differential of `j`. Hence the whole line lies in that image
   (`le_of_finrank_eq_one`). Turn `n` into a base point `g`.
   `comp_innerIso_hom_of_isTransporter` shows that `i` followed by
   conjugation by `g` equals `c` followed by `i`. Write `σ` for `c`
   viewed as an automorphism of the commutative group scheme
   (`commIso`). Then `σ` carries `α` to `-α` on character lattices,
   and `-α` to `α`. By `weightSpace_map_of_transport`, the
   differential of conjugation by `g` maps the weight space of `β`
   onto that of `-β`. Because `H` is normal, this differential
   preserves the image of the differential of `j`
   (`targetMapLinear_innerIso_mem_range`). So the weight spaces of
   `α` and `-α` both lie in that image.

2. **The product of `H` and `T` is `G`.** Since `T` normalizes `H`,
   `exists_smoothConnected_fppfProduct` supplies a smooth connected
   closed subgroup `p : P → G` that is the fppf product of `H` and
   the torus. Its differential image contains the images of the
   differentials of `j` and `i` (`range_targetMapLinear_le`). It
   therefore contains every ambient weight space. The root spaces
   come from step 1. The zero weight space comes from
   `zeroWeightMap_surjective_of_selfCentralizing`. The remaining
   weight spaces are zero by the root hypothesis. The ambient weight
   spaces span `Lie(G)` (`isInternal_weightSpace_of_isSplitTorus`).
   So the differential of `p` is surjective, and smooth tangent
   subgroup equality (`isIso_of_surjective_targetMapLinear`) makes
   `p` an isomorphism.

3. **The inversion is the identity.** Let `x` be a point of `T` on a
   test scheme. The base point `g`, restricted to that test scheme,
   lies in the range of the isomorphism `p`. So, after a flat
   surjective locally finitely presented refinement `v`, it equals
   `h t` with `h` a point of `H` and `t` a point of the range of `i`.
   Let `s` be the pullback of `x` along `v`.
   `comp_eq_self_of_constantPoint_eq_mul` computes that
   `i(c(s)) = g i(s) g⁻¹ = h i(s) h⁻¹`, using that `t` commutes with
   `i(s)`. Hence `i(c(s) s⁻¹) = h (i(s) h⁻¹ i(s)⁻¹)`. This point lies
   in `H` by normality, and it lies in the range of `i`. Because the
   intersection of `H` with the range of `i` is the bottom subgroup,
   `c(s) = s`. A flat surjective morphism of schemes is an
   epimorphism, so `c(x) = x`. Since `x` was arbitrary, `c` is the
   identity.

4. **`α = -α`.** Substituting `c = 1` into `α ∘ c = -α` gives
   `α = -α` in the character lattice.

5. **Contradiction.** `eq_zero_of_eq_neg` transports the character
   lattice of the split torus to `I → ℤ` and concludes `α = 0`, which
   contradicts `α ≠ 0`.

Every weight of `Lie(H)` therefore vanishes, so `Lie(H)` is zero. By
smooth tangent subgroup equality the identity section of `H` is an
isomorphism, so the range of `j` is the bottom subgroup. This is
exactly the existing radical predicate.

## Provenance

The proposition is derived from Brian Conrad, *Reductive group
schemes* (2014), proof of Proposition 3.1.9, pp.87–88. The implemented
route differs from the source. The source passes to the quotient by
the reduced codimension-one subtorus `(ker α)^0_red` and uses that a
nonsolvable smooth connected affine group of dimension three has
trivial unipotent radical. Neither step is formalized here. Instead
the proof argues directly with the Lie weights of a normal unipotent
subgroup and the fppf product of that subgroup with the torus, as
described above. The proof uses no characteristic restriction and no
primitivity of `α`. It does not use the rank-one root reducedness or
Weyl image results, which assume reductivity. The helper statements in
the namespace `RankOneWeylCriterion` are internal lemmas for this
argument.
