# The Hasse–Arf theorem for an abelian group

`Langlands.LocalFactor.Ramification.HasseArf.Abelian`. The Hasse–Arf theorem for a finite abelian
group acting on a discrete valuation ring: at every break `i` of the lower filtration, `φ(i)` is an
integer. This is the theorem that `Herbrand/HasseArfProof.lean` specialises to the Library's
`Langlands.Ramification.Padic.HasseArfIntegrality` for finite abelian extensions of p-adic fields.

## Statements

Name space `Langlands.Ramification`.

```lean
theorem hasseArfChain_lowerGroup_of_isMulCommutative
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    HasseArfChain (lowerGroup R G)
```

It follows from the reduction to cyclic quotients, `hasseArfChain_lowerGroup_of_forall_isCyclic_quotient`:
under the same hypotheses, if the Hasse–Arf property holds for `G ⧸ H` acting on
`FixedPoints.subring R H` for every `H` with cyclic quotient, it holds for `G`.

## Proof

*Reduction.* Let `i ≥ 1` be a break and `g ∈ G_i` not in `G_{i+1}`. A finite abelian group has a
subgroup `H ⊇ G_{i+1}` not containing `g` with `G ⧸ H` cyclic (`exists_normal_isCyclic_quotient`, via a
character that is non-trivial on `g`). Put `v = φ_G(i)`. By the compatibility of the upper numbering
with quotients (`upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq` and Herbrand's theorem
`map_lowerGroup_mk_eq_of_isSeparable_residueField`), `(G/H)^v` is the image of `G^v = G_i`, which
contains the class of `g`, while `(G/H)^w` is the image of `G^w ≤ G_{i+1} ≤ H` for `w > v`
(`upperGroupRat_le_succ_of_lt`), hence trivial. So `v` is the last break of the upper filtration of
`G/H`, which is `φ_{G/H}(c)` for a lower break `c` of `G/H` (`exists_jump_of_upper`); by the cyclic
case `φ_{G/H}(c)` is an integer (`exists_herbrandPhiRat_eq_natCast`), so `φ_G(i)` is an integer, which
is the divisibility (`dvd_of_herbrandPhiRat_eq_natCast`).

*The abelian theorem.* For `H` with cyclic quotient, `R^H` is a discrete valuation ring
(`isDiscreteValuationRing_fixedSubring`) on which `G ⧸ H` acts with all the hypotheses
(`faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring`), so
`hasseArfChain_lowerGroup_of_isCyclic` applies.

## Declarations

In the order of the file, in `Langlands.Ramification.HasseArf.Abelian`: `upperGroupRat_le_succ_of_lt`,
`exists_jump_of_upper`, `exists_herbrandPhiRat_eq_natCast`, `dvd_of_herbrandPhiRat_eq_natCast`,
`exists_normal_isCyclic_quotient`; then, in `Langlands.Ramification`,
`hasseArfChain_lowerGroup_of_forall_isCyclic_quotient` and
`hasseArfChain_lowerGroup_of_isMulCommutative`.

## Source and licence

Adapted from four files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean` | `dfc9e1e61ff072ddd85550fa687ebb2f733c9565856f93eb692ac0298954fe08` |
| `P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean` | `b0ba21b611119d1b594897931772e9b67e815a2402394866a80cb4692d26effe` |
| `Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean` | `da36162e438f9865b42c03b3f9b46e9bdd28d0f918b802ab2b2b50c2e7e5a4db` |
| `P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean` | `e9875d4e8cf98ae5fdd97d5235ea61acb96fb08e007dc36816aeb30a3717efa6` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files: the four files are one module; the FLT proof name space
`P2MW.<file>.HasseArfRed` is `Langlands.Ramification.HasseArf.Abelian`; upstream's
`IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient` and
`…_of_isMulCommutative` are `Langlands.Ramification.hasseArfChain_lowerGroup_of_forall_isCyclic_quotient`
and `…_of_isMulCommutative`, stated on `lowerGroup` (definitionally equal statements; the instance
proofs inside differ, the FLT statement files having erased two `simp` lemmas and, for the
`ValuationSubring` versions, lemmas that are not ported). The erasure of the `simp` lemmas
`lowerGroup_subgroupOf` and `lowerGroup_map_subtype` is kept for each proof, in its section. The
deprecated `SetLike.exists_of_lt` and `push_neg` are replaced by `IsConcreteLE.exists_of_lt` and
`push Not`; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter V, §7, Theorem 1 (Hasse–Arf), printed page 93: if `G`
is abelian, the jumps of the upper filtration are integers; Theorem 1′, printed page 94, is the
lower-numbering form proved here, and the reduction to a cyclic quotient through Herbrand's theorem
is Serre's, on the same page. Chapter IV, §3, Proposition 14 (printed page 74) and Lemma 5
(Herbrand's theorem, printed page 75) for the compatibility of the numberings with quotients used
in the reduction. Serre assumes `K` complete and the residue extension separable; the theorem here
is for a finite group acting faithfully on a discrete valuation ring with perfect residue field.
