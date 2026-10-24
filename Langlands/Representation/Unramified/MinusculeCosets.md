# Left cosets in a minuscule spherical double coset

Module `Langlands.Representation.Unramified.MinusculeCosets`, namespace
`Langlands.Unramified.MinusculeCosets`.

## Setting

`F` is a field with a valuation `v` (values in a linearly ordered commutative group with
zero), and `ϖ : Fˣ` is a uniformizing element (`IsUniformizingElement v ϖ` from
`Langlands.Representation.Whittaker.Iwasawa`). Write `K = integralSubgroup v.integer n`
for the integral invertible matrices of size `n + 1`. For a subset `S` of the coordinates,
`t_S = subsetTorus ϖ S` is the diagonal matrix with `ϖ` in the positions of `S` and `1`
elsewhere. Only the Iwasawa decomposition of that module is used; no local-field
hypothesis enters this module.

This module is internal infrastructure for the spherical Hecke computation. It formalizes
the standard explicit decomposition of the double coset `K t K`, where `t = t_S'` is a
minuscule coweight, into left cosets `x K`. Compare Gross, *On the Satake isomorphism*
(1998), section 3, and Borel, *Automorphic L-functions* (1979), section 7. The Lean route
below is self-contained.

## Radical matrices and representatives

- `IsRadicalPair S a b` means `a ∈ S`, `b ∉ S` and `a < b`. `radicalPart S c` is the
  matrix with entries `c a b` at the radical pairs and `0` elsewhere. Its square is zero
  (`radicalPart_mul`), so `radicalElement S c = 1 + radicalPart S c` is invertible with
  inverse `radicalElement S (-c)`, and it is upper unipotent.
- `cosetRep ϖ S c = radicalElement S c * subsetTorus ϖ S`.
- `torusConj_apply`: conjugating `radicalElement S c` by `t_S` divides the radical entries by
  `ϖ`. Hence `torusConj_mem` holds: if `v (c a b) < 1` on the radical pairs, the conjugate is in
  `K`. Conversely, `lt_one_of_torusConj_mem` holds.
- `subsetTorus_conj` and `exists_perm_mem_iff`: a permutation matrix (`Cartan.permGL`)
  conjugates `t_S` to `t_S'` whenever `|S| = |S'|`.

## Membership and distinctness

- `cosetRep_mem_doubleCoset`: if `|S| = |S'|` and the radical entries of `c` are integral,
  then `cosetRep ϖ S c ∈ K t_S' K`.
- `cosetRep_inv_mul_mem_of_congr`: two representatives with the same subset lie in the same
  left coset when their radical entries are congruent modulo the maximal ideal.
- `eq_of_cosetRep_inv_mul_mem`: conversely, if two representatives lie in the same left coset,
  their subsets are equal. This uses uniqueness of the Iwasawa torus exponent,
  `iwasawa_exponent_unique`, together with `subsetExponent_injective`. Their radical entries
  are then congruent.

## Covering

`exists_cosetRep_of_mem_doubleCoset`: every `g ∈ K t_S' K` satisfies
`(cosetRep ϖ S c)⁻¹ * g ∈ K` for some `S` with `|S| = |S'|` and some integral `c`. The proof
goes as follows.

1. Write `g = u t_λ k` by the Iwasawa decomposition `exists_iwasawa`.
2. The entries of `b = u t_λ` are integral, and so are those of `ϖ b⁻¹`
   (`doubleCoset_entry_mem`, `doubleCoset_inv_entry_mem`). Hence every exponent is `0` or `1`
   (`exponent_eq_zero_or_one`), so `t_λ = t_S`.
3. Valuations of determinants give `|S| = |S'|`.
4. `exists_cosetRep_of_bounds` finishes the proof. It replaces the columns of `u` indexed by
   `S` with unit vectors, which gives a matrix `U ∈ K`. It also keeps the block of `u` with
   rows and columns outside `S`, which gives `E ∈ K` commuting with `t_S`. It then checks
   that `b⁻¹ U t_S` is integral, and reads off the radical entries `c`.

## Labelled representatives

Let `Λ` be a type with a map `σ : Λ → F` (in the application, residue classes with chosen
lifts).

- `RadicalPairs S` is the type of radical pairs of `S`. `liftCoeff σ S w` puts `σ (w p)` at
  each radical pair `p`.
- `CosetIndex Λ m i` is the sigma type of a subset `S` with `S.card = i` and a labelling
  `w : RadicalPairs S → Λ`. `labelledRep ϖ σ α = cosetRep ϖ S (liftCoeff σ S w)`.
- `labelledRep_mem_doubleCoset`: if every `σ x` is integral, then every labelled
  representative of size `i` lies in `K t_S' K` whenever `|S'| = i`.
- `labelledRep_unique`: assume that distinct labels have lifts at distance one
  (`v (σ x - σ y) < 1 → x = y`). Then two labelled representatives whose left cosets both
  contain `g` are equal.
- `exists_labelledRep`: assume that every integral element is congruent to some `σ x`. Then
  every element of `K t_S' K` lies in the left coset of a labelled representative.

Together, `K t_S' K` is the disjoint union of the left cosets `x_α K` with
`α : CosetIndex Λ (n + 1) |S'|`.
