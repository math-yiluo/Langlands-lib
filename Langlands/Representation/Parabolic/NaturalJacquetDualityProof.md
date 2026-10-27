# Proof of natural upper/opposite normalized Jacquet duality

This module proves `Langlands.Parabolic.NaturalNormalizedJacquetDualityStatement`
as the theorem `Langlands.Parabolic.naturalNormalizedJacquetDuality`, the pair of
`standardNaturalJacquetDuality` (the standard clause for the standard parabolics of
`GL_n`) and `refinedNaturalJacquetDuality` (the refined clause for the product
parabolics of a block refinement inside a block Levi). Both clauses are obtained by
instantiating the abstract stable evaluation pairing of
`Langlands.Representation.Jacquet.StablePairingProof`. That pairing is a form of
Casselman's canonical pairing (Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
`casselman-2019-jacquet-module`, Section 6, Theorem III.6.2 and Corollary III.6.3,
pages 7–8). The constructions in this module (pairing data, Iwahori lemmas and the
transport identities) are internal to this project and add no statement to the
Library.

The equivalences are existential. For each field, topology and parabolic, one
contracting tuple is fixed. Every admissible input then receives the stable pairing
built from that tuple, and the family `E` is chosen from these pairings. The proof
adds no hypotheses: admissibility of `π` (or of the Levi representation in the
refined clause) is the only assumption on the input. Rank zero and one-block shapes
are not treated separately.

## Iwahori conjugation lemmas

For a block shape `B`:

- `blockScalar_commute_of_mem_leviSubgroup`: the block scalar of a tuple commutes
  with every element of the embedded Levi subgroup, from `blockScalarLevi_commute`.
- `inv_conj_conj_of_commute`: in any group, conjugation by `m` commutes with
  conjugation by an element that commutes with `m`.
- `hasBlockIwahoriFactorization_conj`: if `K` has block Iwahori factorization and
  `m` lies in the embedded Levi subgroup, then so does `m K m⁻¹`
  (`Jacquet.conjOpenSubgroup m K`). The factorization of `m⁻¹ k m` in `K` is
  conjugated back by `m`. The lower, Levi and upper pieces stay in their subgroups
  because the Levi normalizes both radicals. The contraction conditions for weakly
  contracting tuples follow from those of `K`, by the commutation lemma.
- `HasBlockIwahoriFactorization.factor`, `.lower_conj` and `.upper_conj_pow`
  unpack the factorization `k = l m u` inside `K`. They also unpack the inclusions
  `g⁻¹ (K ∩ Nbar) g ⊆ K` and `gʳ (K ∩ N) g⁻ʳ ⊆ K` for the block scalar `g` of a
  weakly contracting tuple; the second is proved by induction on `r`.
- `eventually_pow_conj_mem`: for a strictly contracting tuple, a compact set of
  upper unipotent elements and an identity neighborhood `U`, all sufficiently high
  powers of the block scalar conjugate the set into `U`. This is the Library's
  `uniformCompactBlockContraction` together with `strictPowersEventuallyDeep`.

## Standard pairing data

For a strictly contracting tuple `a`, `standardPairingData F T B a ha` is the
`Jacquet.StablePairingData` on `GeneralLinear n F.Carrier` with

- `N = B.unipotentSubgroup`, `Nbar = B.oppositeUnipotentSubgroup` and
  `M = B.leviSubgroup`, with the Library normalizer facts;
- `g = B.blockScalar a`, commuting with `M` by the first lemma;
- good subgroups the compact open subgroups with block Iwahori factorization.
  These form a neighborhood basis
  (`exists_compactOpenSubgroup_hasBlockIwahoriFactorization`), are stable under
  Levi conjugation (`isCompact_conjOpenSubgroup` and the conjugation lemma), and
  satisfy the factorization, conjugation and depth axioms through the lemmas above.

`standardPairingData_admits` shows that every admissible `ρ` satisfies `Admits`.
Fixed spaces are finite-dimensional by admissibility. The smooth contragredient is
admissible by `isAdmissible_smoothContragredient_of_compact_cofinal`, since compact
open subgroups are cofinal. The upper surjectivity and kernel conditions for the
dual come from the Library's `blockStableImageJacquetBijective` and
`blockPowerKernelJacquet`. The opposite conditions for `ρ` come from
`blockOppositeStableImageJacquetBijective` and `blockOppositePowerKernelJacquet`.
Only the surjective half of bijectivity and one inclusion of the kernel equality
are used.

Three transport identities connect the target constructions with the ambient
quotients of the pairing data:

- `jacquetModuleEquiv_normalizedJacquet`: under the Library identification
  `B.jacquetModuleEquiv` of the internal-radical upper quotient with the ambient
  quotient by `B.unipotentSubgroup`, the normalized Levi action of
  `T.normalizedJacquet B` becomes `inverseHalfCharacter (T.leviModulus B) l` times
  the descended action of `B.leviEquiv l` (from `normalizedJacquet_mk`).
- `jacquetModuleEquiv_normalizedJacquetMap`: under the same identification,
  `T.normalizedJacquetMap B f` becomes `Jacquet.map` for the upper radical.
- `oppositeJacquet_ρ_apply`: the action of
  `CuspidalJacquetMultiplicity.oppositeJacquet T B π` at `l` is the inverse half
  character of the inverse modulus `δ⁻¹` at `B.leviEquiv l` times the descended
  action, where `δ` is `T.leviModulus B` transported to the embedded Levi.

These identities are checked on quotient representatives, and the two quotient
presentations are kept distinct.

## The standard clause

`inverseHalfCharacter_mul_inverseHalfCharacter_inv` shows that the inverse half
characters of `δ` and `δ⁻¹` multiply to `1`. In `standardNaturalJacquetDuality`,
the Library's `deepChamberNonempty` gives a deeply contracting, hence strictly
contracting, tuple `a`. Let `χO` be the opposite character
`inverseHalfCharacter δ⁻¹ ∘ B.leviEquiv`. Its kernel is open, because the kernel of
`T.leviModulus B` is open (`isOpen_ker_leviModulus`) and `B.leviEquivContinuous` is
a homeomorphism. Its product with the upper character
`inverseHalfCharacter (T.leviModulus B)` is `1` by the previous lemma.

For each admissible `π`, `exists_isStablePairing` gives a stable pairing `b_π` for
the standard data. `IsStablePairing.exists_equiv`, with `ι = B.leviEquivContinuous`,
the two characters, `σU = T.normalizedJacquet B (D π)`,
`eX = B.jacquetModuleEquiv (D π)` and `σO` the action of `oppositeJacquet T B π`,
gives a representation equivalence `E_π` with `E_π x y = b_π (eX x) y`. The two
compatibility hypotheses are the first and third transport identities.

The family `E` is chosen from these equivalences. For an intertwiner `f : π → τ`,
`x` in the upper module of `D τ` and `y` in the opposite quotient of `π`, the
naturality equation becomes
`b_π (eX (r_P(D f) x)) y = b_τ (eX x) (Jacquet.map f y)`. The second transport
identity rewrites the left side as `b_π (Jacquet.map (D f) (eX x)) y`, and
`IsStablePairing.natural` proves the equality.

## Refined pairing data

For a block refinement `S` of `B`:

- `conjOpenSubgroup_leviPiOpenSubgroup`: conjugating the product open subgroup
  `CuspidalSupport.leviPiOpenSubgroup T B K` by `m` gives the product of the
  blockwise conjugates.
- `refinedPairingData F T B S a ha`, for tuples `a i` strictly contracting for
  `S i`, is the stable pairing data on `B.Levi F.Carrier` with
  `N = refinedUnipotent`, `Nbar = refinedOppositeUnipotent`, `M = refinedLevi`, and
  `g` the tuple of block scalars `fun i => (S i).blockScalar (a i)`. Its good
  subgroups are the products `leviPiOpenSubgroup T B Kf` of compact open
  `Kf i` with block Iwahori factorization for `S i`. They form a neighborhood basis
  (`CuspidalSupport.exists_leviPiOpenSubgroup_subset`) and are compact
  (`isCompact_leviPiOpenSubgroup`). Every axiom is checked blockwise from the
  standard lemmas. Depth uses the maximum over blocks of the exponents from
  `eventually_pow_conj_mem`.
- `refinedPairingData_admits`: every admissible representation of the block Levi
  satisfies `Admits`. Its smooth contragredient is admissible because compact open
  subgroups of the Levi are cofinal (`levi_exists_compact_openSubgroup_subset`). The
  upper conditions for the dual come from `refinedStableImageJacquetBijective` and
  `refinedPowerKernelJacquet` of
  `Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof`. The opposite
  conditions come from the Library's `refinedOppositeStableImageJacquetBijective`
  and `refinedOppositePowerKernelJacquet`.

## The refined clause

`refinedNaturalJacquetDuality` chooses strictly contracting tuples `a i` blockwise
by `deepChamberNonempty`. The opposite character is
`inverseHalfCharacter (T.refinedOppositeLeviModulus B S)`. Its kernel is open
(`isOpen_ker_refinedOppositeLeviModulus` and `isOpen_ker_inverseHalfCharacter`).
Its product with the upper character `inverseHalfCharacter (T.refinedLeviModulus B S)`
is `1` by `inverseHalfCharacter_mul_inverseHalfCharacter_inv`, because
`T.refinedOppositeLeviModulus B S` is defined as the inverse of
`T.refinedLeviModulus B S`.

For each admissible `π`, `IsStablePairing.exists_equiv` is applied with `ι` the
identity of `refinedLevi`, `eX` the identity, `σU = T.normalizedRefinedJacquet B S
(D π)` and `σO = T.normalizedRefinedOppositeJacquet B S π`. Both compatibility
hypotheses hold by definition; the opposite one is checked on quotient
representatives. Naturality is `IsStablePairing.natural`, evaluated on quotient
representatives of `x` and `y`. Here `normalizedRefinedJacquetMap` and
`normalizedRefinedOppositeJacquetMap` act on representatives as `Jacquet.map`.
