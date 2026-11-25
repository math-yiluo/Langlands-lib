# Subquotients of an antitone filtration by subgroups

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Units`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file sets up the group theory of a decreasing filtration `G ⊇ U^0 ⊇ U^1 ⊇ …` (indexed by ℕ) of an arbitrary group `G`, of the kind formed by principal-unit subgroups, and proves the counting rule that the order of `U^l/U^n` is the product of the orders of the graded pieces `U^i/U^(i+1)`.

## Definitions

- `AntitoneSubgroupFiltration G`: a structure holding subgroups `subgroup n` with `subgroup n ≤ subgroup m` for `m ≤ n`. `principalUnitSubgroup n` is just `subgroup n`.
- `quotient_principalUnitSubgroup_mapOfLe`: for `m ≤ n` and `U^m`, `U^n` normal, the natural surjection `G/U^n →* G/U^m`.
- `principalUnitSubgroupClassInQuotient m n`: the image of `U^m` in `G/U^n`.
- `principalUnitSubquotient m n`: the quotient of `U^m` by `U^n ∩ U^m` (`subgroupOf`), with its group structure, commutative when `G` is; `principalUnitGradedPiece n` is the case `U^n/U^(n+1)`. Class maps, lifts and an induction principle come with them.

## Results

- The map `G/U^n → G/U^m` is surjective with kernel the class of `U^m` (`quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient`); it composes transitively and is the identity for `n ≤ n`.
- `principalUnitSubquotientEquivClassInQuotientOfLe`: for `m ≤ n`, `U^m/U^n` is isomorphic to the class of `U^m` in `G/U^n`.
- `quotientModuloPrincipalUnitClassEquivQuotientOfLe`: the third isomorphism theorem `(G/U^n)/(U^m/U^n) ≃ G/U^m`.
- `card_principalUnitSubquotient_eq_mul_of_le`: for `l ≤ m ≤ n`, `#(U^l/U^n) = #(U^m/U^n) · #(U^l/U^m)`, given normality of `U^m`, `U^n` and finiteness of the three subquotients.
- `card_principalUnitSubquotient_eq_prod_gradedPiece`: `#(U^l/U^(l+r))` is the product over `i < r` of `#(U^(l+i)/U^(l+i+1))`.

Many further lemmas give membership, kernel and equality criteria in these quotients, in right-quotient (`x / y`) and left-quotient (`y⁻¹ * x`) forms.

## Proofs

The three-level count comes from restricting `G/U^n → G/U^m` to classes, identifying its kernel with `U^m/U^n` and applying the first isomorphism theorem with `Subgroup.card_mul_index`; the product formula follows by induction on `r`.

## Watch for

- Despite the names, no valued field appears: the structure is a bare filtration, and nothing asserts it comes from units of a valuation ring.
- Normality of the relevant levels is a typeclass hypothesis throughout; the product formula takes normality of every level as an explicit argument and finiteness of every subquotient `U^i/U^j` as an instance.
- `principalUnitSubquotient m n` is defined for all `m`, `n`; it is the usual subquotient only when `m ≤ n`.
- Cardinalities are `Nat.card`, so the finiteness hypotheses are what make them meaningful.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`: the Lean file is the source byte for byte (SHA-256 `a6cc02a7b0ae4fdaff767978c620263136671df8686fc8a899aa0e4f09246056`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
