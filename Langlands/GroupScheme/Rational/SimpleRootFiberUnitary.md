# Unitary coordinates on the simple-root fiber of a multipliable relative root

Module `Langlands.GroupScheme.Rational.SimpleRootFiberUnitary`, namespaces
`Langlands.GroupScheme.SplitPinning.PartnerData` (generic part) and
`Langlands.GroupScheme.SimpleRootFiber` (fiber part).

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SU3 half.

## Purpose

This module supplies the hypotheses of the modules `PartnerOrbitUnitaryCoordinates`
and `PartnerOrbitRootProducts` for one simple relative root `a`, in the case where `2 • a` is
also a relative root. The input is the setting of `SimpleRootFiberPinning`: a maximal split
torus `f ≫ j`, its torus centralizer `j : T ⟶ G`, a finite Galois splitting field `K`, a
reduced root datum `P` of `j_K`, and a generic cocharacter `ν` for which `a` is simple. In this
setting the absolute roots over `a` form the fiber `Oₐ` of simple roots
(`SimpleRootFiberPinning`). Module `SimpleRootFiberPartners` pairs each member `t` of `Oₐ`
with an `A₂` partner `π t`. The roots over `2 • a` are the sums `t + π t`.

This module provides:

1. the partner structure `fiberPartnerData` on `Oₐ`;
2. the identification of the piece enumerations of `PartnerOrbitRootProducts` with the roots
   over positive multiples of `±a` and `±2a`, together with their injectivity;
3. the four instances of the published `Geometry.Building.SplitRelativeRootGroupProductStatement`
   for these enumerations, taken as a hypothesis `hProd`, and from them the hypotheses
   `hmem`, `hprod`, `huniq`, `hmem2`, `hprod2` of `PartnerOrbitUnitaryCoordinates`;
4. the character of `T` over the fiber field for the negative root `-a`.

This is the standard description of root groups of quasi-split groups. See Borel–Tits,
*Groupes réductifs*, §4, and Kaletha–Prasad, *Bruhat–Tits theory*, Prop. 7.1.1 and its proof.
The Lean development is internal. Every step is proved here or taken from the Library.

## Generic lemmas (namespace `SplitPinning.PartnerData`)

For `D : PartnerData O` and an enumeration `e : D.orientation ≃ Fin n`:

- `pieceRev` (def): reversal of the three positions inside each piece of `Fin (n * 3)`;
  `pieceRev_pieceRev`.
- `lowerPieceEnum_eq_neg`: `D.lowerPieceEnum e k' = -D.upperPieceEnum e (pieceRev k')`.
  Consequences: `mem_range_lowerPieceEnum_iff` (`χ` is a lower piece root iff `-χ` is an
  upper one) and `lowerPieceEnum_injective`.
- `doubleRoot_injective`: the sums `r + π r` of different pieces are different. The proof
  pairs with the coroot of `r`. This gives `2 - 1 = 1` on the piece of `r`. It gives `0` on
  any other piece, because the members of different pieces are orthogonal
  (`PartnerData.orthogonal`).

## The fiber (namespace `SimpleRootFiber`)

The variables are those of `SimpleRootFiberPartners`, with `h2a : 2 • a ∈ relativeRoots`.
Write `Dₚ` for `fiberPinning`, `Oₐ` for the fiber of `a` and `π` for `partner`.

### Partners (section `Partners`)

- `fiberPartnerData` (def): the `PartnerData Oₐ` with partner map `π`. Its fields are
  `partner_mem`, `partner_partner`, `partner_ne`, `pairing_partner` and
  `isOrthogonal_of_ne_partner` of `SimpleRootFiberPartners`. `fiberPartnerData_partner`
  (`rfl`).

### Enumerations (section `Enumerations`)

- `add_partner_mem`: for `t ∈ Oₐ`, `t + π t` is a root of `j_K`, and its restriction is
  `2 • a`.
- `fiberOrientationEquiv` (def, written `eπ`): an enumeration of the orientation.
- `orientation_mem`: members of the orientation lie in `Oₐ`.
- `eq_one_or_two_of_restrict` (needs a relative root system `hR`): a root restricting to
  `m • a` with `m > 0` has `m = 1` or `m = 2`, by `HasRelativeRootSystem.eq_one_or_two_of_nsmul_mem`.
- `mem_range_upperPieceEnum_iff`: the upper piece enumeration lists exactly the roots of
  `j_K` whose restriction is a positive multiple of `a`. Roots over `a` are members of `Oₐ`
  (`exists_mem_fiberSet`). Each is in the orientation or is the partner of a member of it.
  Roots over `2 • a` are sums `t + π t` (`exists_mem_root_eq_add_partner`).
- `upperPieceEnum_injective`: distinct positions carry distinct roots. Positions over `a` and
  over `2 • a` are separated by their restrictions, because `a ≠ 2 • a`. Two positions over
  `a` are compared through the orientation. Two positions over `2 • a` are compared by
  `doubleRoot_injective`.
- `mem_range_lowerPieceEnum_iff` (fiber version): the same for `-a`.
  `mem_range_doubleRoot_iff`, `mem_range_neg_doubleRoot_iff`: the sums of the pieces, and
  their negatives, list exactly the roots over positive multiples of `2 • a`, respectively
  `2 • -a`. This again uses `eq_one_or_two_of_restrict`.

### Products (section `Products`)

Here `hProd : SplitRelativeRootGroupProductStatement` and
`hAdj : AdjacentSimpleRootSpecialLinearStatement` are hypotheses. Write `UK[b]` for the
rational points of the relative root group of `b` for the scalar extension of `f ≫ j`.

- `fiberUpperProduct`, `fiberLowerProduct`: the statement `hProd` for the upper and lower
  piece enumerations. Each gives the ordered product description of `UK[a]`, respectively
  `UK[-a]`, with unique factors. `fiberDoubleProduct`, `fiberNegDoubleProduct`: the product
  description of `UK[2 • a]` and `UK[2 • -a]` by the (negated) sums of the pieces.
- `fiber_hmem_upper`, `fiber_hprod_upper`, `fiber_huniq_upper`, `fiber_hmem_lower`,
  `fiber_hprod_lower`, `fiber_huniq_lower`, `fiber_hmem2_upper`, `fiber_hprod2_upper`,
  `fiber_hmem2_lower`, `fiber_hprod2_lower`: the hypotheses of the same names in
  `PartnerOrbitUnitaryCoordinates`, for `fiberPartnerData`, the root maps of `Dₚ` and `a`.
  They are the abstract lemmas of `PartnerOrbitRootProducts` applied to the four product
  statements.

### Characters (section `Characters`)

Write `p₀` for the base point of the fiber, `β₀` for its root, `L₀` for the fiber field (the
field of `β₀`) and `E₀` for the pair field (module `SimpleRootFiberPartners`).

- `galoisRepresentation_partnerRoot`: every automorphism of `K` over `L₀` fixes the root of
  `π p₀`. It fixes `p₀`, and the partner map commutes with the Galois action.
- `partnerCharacter` (def): the root of `π p₀`, descended to a character of `T` over `L₀` by
  the Library `AffineCharacterTowerDescent.fixedDescend`.
- `partnerCharacter_eval`: at a rational point `z` of `T`, its value is the conjugate, over
  `E₀`, of the value of the root-orbit character of `β₀`. The proof uses the embedding of `L₀`
  attached to `π p₀`, which is the inclusion composed with the conjugation
  (`fiberEmbedding_partner`, `fiberEmbedding_basePoint`).
- `fiberEmbedding_neg_partnerCharacter`: for `b ∈ Oₐ`, the embedding attached to `b` sends
  the value of `-partnerCharacter` at `z` to the inverse of the value of the root of `π b` at
  `z`. This is the hypothesis of `conj_unitaryRho_lower` in `PartnerOrbitUnitaryCoordinates`.
