# Cell data in semisimple rank one

This internal supporting unit supplies the cell data for the rank-one case of
`SplitRankOneCommonTorusIsomorphismStatement`. Let `i : T ⟶ G` be a maximal
torus of a connected reductive group `G` over a field `k`, with `T` split, and
assume that any two roots of `i` are linearly dependent over `ℤ` (the rank-one
hypothesis `hrank`). For a root `α` and a cocharacter `ν` with `⟨α, ν⟩ > 0`, it
shows that the dynamic centralizer of `ν` is `T`, and that the dynamic
unipotent subgroup of `ν` is a copy of `𝔾ₐ` on which `T` acts through `α`.
This is the rank-one case of Milne, *Algebraic Groups* (2017), Definition 21.10
and Theorem 21.11(c) (p. 428–429): the root group `U_α = U_G(ν)` is isomorphic
to `𝔾ₐ` and normalized by `T`.

Three published Prop-valued statements enter as explicit hypotheses. The
final candidate must discharge them with their Library proofs:

- `hDCR : DynamicCentralizerReductiveStatement`: a closed subgroup that
  represents the dynamic centralizer of a cocharacter of a connected reductive
  group is connected reductive.
- `hPRU : RankOnePositiveRootUniquenessStatement`: in semisimple rank one,
  two roots that pair positively with the same cocharacter are equal.
- `hLL : SplitRootLieLineStatement`: every root space of a split maximal torus
  is a line.

No other premise is added. In particular the results assume no root-group,
big-cell or pinning data.

## Line coordinates (namespace `RankOneCellData`)

Let `H` be an affine group over `k` and `c` a coordinate function on it. Here
`lineValue c v` is the value of `c` at a point `v : U ⟶ H.X` over a test
scheme `U`, defined by pulling back `coordToSections H c` along `v`.

- `unit_appTop_eq` and `lineValue_unit_comp`: pulling back along the
  affinization unit of `U` identifies `lineValue` with the coordinate of the
  affinized point (`Lie.pointCoordinates`). `lineValue_eq` restates this for
  `Lie.affinizationFactor`.
- `lineValue_mul`: if `c` is additive on affine points, then `lineValue c` is
  additive on the points over every test scheme. The proof factors `v * w`
  through the affinization unit.
- `lineValue_bijective`: if `aeval (fun _ : Fin 1 => c)` is bijective, so `c`
  freely generates the coordinate algebra, then `lineValue c` is bijective
  over every test scheme. Injectivity comes from `MvPolynomial.algHom_ext` and
  injectivity of `Lie.pointCoordinates`. For surjectivity, a global function
  `a` is the value of the point whose coordinate homomorphism sends `c` to
  `a`.
- `lineCoordinates`: from these two facts, the multiplicative equivalence
  `(U ⟶ H.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤))`.
  `isNaturalVectorCoordinates_lineCoordinates` shows it is natural (this holds
  by definition).
- `pointsEquiv_unit_comp` and `lineValue_act`: if `c` lies in the weight space
  of a character `χ` for a torus action `b`, then
  `lineValue c (b.act s v) = χ(s) * lineValue c v` over every test scheme.
  `isWeightVectorCoordinates_lineCoordinates` packages this as
  `RelativeRoot.IsWeightVectorCoordinates b χ`.

## `latticePairing_ne_zero_of_rankOne`

Under `hrank`, if `⟨α, ν⟩ ≠ 0` for a root `α`, then `⟨β, ν⟩ ≠ 0` for every
root `β`. Proof: a nontrivial relation `s • α + t • β = 0` with `⟨β, ν⟩ = 0`
forces `s = 0`, so `t ≠ 0` and `t • β = 0`. After `toRat` this gives
`β = 0`, by injectivity of `toRat` on the character lattice of a split torus
(`IsSplitTorus.character_toRat_injective`). But roots are nonzero.

## `rankOne_centralizer_isRepresentedBy`

Under `hDCR` and `hrank`, if `⟨α, ν⟩ ≠ 0` for a root `α`, then `i`
represents `Dynamic.centralizer (groupHom ν ≫ i)`. Proof:

1. `Dynamic.Affine.centralizerHom` is a closed subgroup `z` representing the
   centralizer. By `hDCR` it is connected reductive.
2. `i` factors through `z` as `t` (`range_le_centralizer_groupHom_comp`,
   `liftOfLE`), and `t` is a maximal torus of the centralizer
   (`IsMaximalTorus.of_comp`).
3. `dynamicCentralizerRoots` identifies the roots of `t` with the roots `β` of
   `i` with `⟨β, ν⟩ = 0`. By `latticePairing_ne_zero_of_rankOne` there are
   none.
4. The rank-zero result `IsConnectedReductive.isIso_of_roots_eq_empty` (module
   `SplitRankZeroIsomorphism`) makes `t` an isomorphism. Hence `i = t ≫ z`
   represents the centralizer (`IsRepresentedBy.precomp_iso`).

## `rankOne_exists_rootGroup`

Under `hPRU`, `hLL` and `hrank`, if `⟨α, ν⟩ > 0` for a root `α`, there is a
homomorphism `x : VectorGroup.groupScheme k 1 ⟶ G` that represents
`Dynamic.unipotent (groupHom ν ≫ i)` and satisfies
`(t ≫ i) * (a ≫ x) * (t ≫ i)⁻¹ = weightPointAction α U t a ≫ x` for all
points `t` of `T` and `a` of `𝔾ₐ` over every test scheme `U`. Proof:

1. `Standard.unipotentScheme i ν ∅` is smooth and affine, and
   `Standard.unipotentHom i ν ∅` represents the dynamic unipotent subgroup
   (`Standard.isRepresentedBy_unipotentHom_empty`). `T` acts on it by
   conjugation (`Standard.unipotentAction`).
2. `TorusUnipotence.exists_positiveWeight_coordinates` and
   `TorusUnipotence.exists_triangular_mul` give free coordinates
   `t₀, …, t_{d-1}` that are weight vectors of weights `w j`, vanish at the
   identity, and multiply triangularly. The coordinate `j` of a product is
   `x_j + y_j + P_j`, where `P_j` involves only earlier coordinates. These
   are the proved results behind `PositiveTorusTriangularCoordinatesStatement`;
   unlike that statement, they need no characteristic hypothesis.
3. Each weight `w j` has a nonzero weight space, so it is a root with
   `⟨w j, ν⟩ > 0`
   (`Standard.actionWeightSpace_unipotentAction_ne_bot_iff`). By `hPRU` it
   equals `α`. The number of coordinates of weight `α` is the dimension of
   the root space of `α`
   (`TorusUnipotence.finrank_actionWeightSpace`,
   `Standard.finrank_actionWeightSpace_unipotentAction`). By `hLL` that
   dimension is `1`, so `d = 1`.
4. With one coordinate, `P₀` has no variables. Its constant term vanishes
   because the coordinate vanishes at the identity, so `t₀` is additive.
   `lineCoordinates` and `RelativeRoot.vectorGroupIso` then give an
   isomorphism `Φ` from the unipotent subgroup to `𝔾ₐ`, and
   `x = Φ⁻¹ ≫ unipotentHom`.
5. The conjugation formula follows from `lineValue_act` for the weight `α`,
   compared coordinatewise with `VectorGroup.coordinates_weightPointAction`
   (`VectorGroup.points_ext`), together with
   `Standard.unipotentAction_act_comp`.

## `rankOne_exists_oppositeRootGroup`

This is the opposite factor, with the extra hypothesis `-α ∈ roots i`.
Since `groupHom (powerHom (-1)) ≫ groupHom ν ≫ i = groupHom (-ν) ≫ i` and
`⟨-α, -ν⟩ = ⟨α, ν⟩ > 0`, `rankOne_exists_rootGroup` applied to `-α` and `-ν`
gives `x'` representing the dynamic unipotent subgroup of the opposite
cocharacter, with conjugation through `-α`.

## `rankOneCellData`

This is the conjunction of `rankOne_centralizer_isRepresentedBy` (using
`⟨α, ν⟩ ≠ 0`) and `rankOne_exists_rootGroup`, in the form requested for the
rank-one assembly.

## `rankOne_exists_cell`

Under `hDCR`, `hPRU`, `hLL` and `hrank`, if `α` and `-α` are roots and
`⟨α, ν⟩ > 0`, there are `xp xm : 𝔾ₐ ⟶ G` such that `i` represents the dynamic
centralizer of `ν`, `xp` represents the dynamic unipotent subgroup of `ν` and
`xm` that of its opposite `groupHom (powerHom (-1)) ≫ groupHom ν ≫ i`. Also,
`T` acts on `xp` through `α` and on `xm` through `-α`, and
`(Dynamic.tripleCellMultiplication xm i xp).left` is an open immersion. The
first five parts come from the three results above. The open immersion is
`Dynamic.isOpenImmersion_tripleCellMultiplication` (the cell
`U(-ν) × Z(ν) × U(ν) → G` of a smooth affine group; Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, Proposition 2.1.8(3)), applied
to these representatives.

## `rankOne_exists_rootCell`

This is the same conclusion for a root datum `P` of `i` (`IsRootDatumOf i P`)
and an index `r`, with `α = P.root r` and `ν = P.coroot r`. The root `P.root r`
lies in `roots i` because the root set is the range of `P.root`. Its negative is
a root by `IsRootDatumOf.neg_mem_roots`, and
`⟨P.root r, P.coroot r⟩ = 2 > 0` because `P.toLinearMap = latticePairing T`
(`RootPairing.root_coroot_two`).
