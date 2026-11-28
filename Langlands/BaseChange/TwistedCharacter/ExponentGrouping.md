# Grouping σ-stable tempered blocks by real exponent into a standard datum

This module turns a family of σ-stable irreducible tempered blocks with
arbitrary real exponents into an ordered σ-stable tempered Langlands
datum. Sort the blocks by decreasing exponent and induce each maximal run
of equal exponents.

## Order of the induced intertwiner

`inducedSigmaIntertwiner_pow`: for block intertwiners with
`A i ^ d = 1` and `σ ^ d = 1`, the normalized induced σ-intertwiner
`inducedSigmaIntertwiner σ B A` has `d`-th power one. The proof applies
`inducedTwistedIntertwiner_pow_eq_one` to the half-modulus twist of the
tensor intertwiner and uses `leviTensorIntertwiner_pow`.

## Over a p-adic field

- `normalizedProduct_irreducible_tempered`: a normalized product of
  irreducible tempered blocks is irreducible and tempered. Irreducibility
  comes from `glTemperedUnitarity` and
  `Classification.bernsteinUnitaryProductIrreducibility`. Temperedness
  comes from temperedness of the block tensor on the Levi
  (`glBlockTensorTempered`) and `glTemperedInduction`.
- Small equivalences used for casts:
  - `twistDeterminantUnramifiedEquiv`, `twistEquivOfEq` and
    `smoothRepEquivOfEq` turn equal parameters, characters and
    representations into equivalences.
  - `cast_twist_determinantUnramified` and `castTwistEquiv` commute rank
    casts with unramified twists.
  - `unramifiedSmoothCharacter` is `c ^ ord` as a smooth character of
    `Eˣ`, and its composite with the determinant is
    `determinantUnramified`.
- `groupBlockEquiv`: suppose each block of an inner normalized product is
  equivalent to the twist of a fixed block by one character
  `determinantUnramified _ _ c`. Then the product is equivalent to the
  twist by the same character of the inner product of the fixed blocks.
  The proof uses `normalizedProductDeterminantTwistEquiv`.
- `nonempty_unitaryGrouping_equiv`: let `L` be a shape, `e` a permutation
  of its blocks, and `q'` a map from the blocks of the permuted shape
  `L.permute e` to the blocks of a shape `D`. The fibre of `q'` over `j`
  is identified with the blocks of an inner shape `S j` of `D.size j`,
  compatibly with block sizes and matrix indices. Take irreducible
  tempered blocks `δ` and unitary parameters `z` on `D`. Then the normalized product over `L` of
  the blocks twisted by `z (q' (e.symm k))` is equivalent to the
  normalized product over `D` of the twisted inner products. The proof
  has three steps.
  1. Both orderings of the twisted blocks are irreducible
     (`normalizedProduct_unitaryTwist`).
  2. They have the same Jordan–Hölder factors
     (`Parabolic.WholeLeviConjugacyProof.permutedProducts`), hence they
     are equivalent.
  3. `Parabolic.orderedProductRegrouping` regroups the permuted product
     along the fibres, and `groupBlockEquiv` pulls each run's common twist
     outside its inner product.
- `castSigmaIntertwiner` transports a σ-intertwiner along an equality of
  ranks. `castSigmaIntertwiner_pow` says the transport preserves the
  order.
- `exists_groupedTemperedDatum`: let `σ ^ d = 1`, and take σ-stable
  irreducible tempered blocks `δ` on `L` with intertwiners `A k`
  satisfying `(A k) ^ d = 1`, and arbitrary real exponents `x`. The
  theorem gives four things:
  - an ordered tempered Langlands datum `t`;
  - block intertwiners `A'` of order dividing `d`;
  - a map `q` from the blocks of `L` to those of `t.shape` with
    `x k = t.exponent (q k)`;
  - at every unitary parameter `z` on `t.shape`, an equivalence of the
    normalized product of the blocks of `L`, twisted by `z (q k)`, with
    the twisted normalized product of the blocks of `t`.

  The proof sorts the blocks by `Tuple.sort` of `-x` and groups equal
  exponents with `Classification.orderedExponentGrouping`. The blocks of
  `t` are the inner normalized products, which are irreducible and
  tempered. Their intertwiners are the normalized induced intertwiners of
  the transported block intertwiners.

The exponents `x` here are arbitrary real numbers: they need not be
positive or distinct. The Library's `TemperedLanglandsDatum` asks for
strictly decreasing real exponents `u_1 > ⋯ > u_r` (its field
`strictAnti`), and sorting followed by grouping produces exactly that.
Henniart–Lemaire (2011), II.5.8–II.5.9, pp. 106–107, likewise order the
real exponents strictly: a Langlands triplet `(α, Ξ, ψ)` has an
irreducible tempered `Ξ` on the Levi subgroup and a real unramified
character `ψ = η^(a_1) ⊗ ⋯ ⊗ η^(a_m)`, positive with respect to `P_α(E)`,
which means `a_1 < ⋯ < a_m`. That is the opposite direction of the
Library's convention. Grouping equal exponents of an arbitrary family of
tempered blocks produces such data, because a product of irreducible
tempered blocks is irreducible and tempered. Irreducibility comes from
Bernstein (1984), Corollary 8.2 a), p. 89 (a product of irreducible
unitarizable representations is irreducible and unitarizable), since
irreducible tempered representations are unitarizable. Temperedness comes
from the temperedness of normalized induction from tempered data. Equivalence of products under permutation follows the
Library's proof of whole-Levi conjugacy, based on Zelevinsky (1980),
Theorem 1.9.
