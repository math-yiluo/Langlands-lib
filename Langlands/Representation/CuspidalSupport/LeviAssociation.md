# Block counts, transport and association laws for standard Levis

Author: Worker 241.

This module adds, on top of the published
`Langlands.Representation.CuspidalSupport.AssociationLawsProof`, the results
about Levi association that the two-block cuspidal-induction argument uses:

- associated standard Levis have the same number of blocks;
- transport of Levi representations (`transport` of
  `Langlands.Representation.CuspidalSupport.LeviDefinitions`) along the
  identity, inverse and composite permutations;
- dot-notation forms `LevisAssociated.refl/symm/trans` and
  `RepresentationsAssociated.refl/symm/trans` of the published association laws.

All results are internal algebraic consequences of the definitions in
`LeviDefinitions`; no analytic theorem from the literature is used. The
block-count interface supports the two-block argument and makes no
claim beyond the stated Lean theorems.

## Published inputs

`ConjugatesLevi B C w` says that conjugation by the permutation matrix of `w`
maps the embedded standard Levi of `B` onto that of `C`. The module uses these
published facts:

- `conjugatesLevi_one`, `leviConjugation_one`, `leviConjugation_inv_symm`,
  `leviConjugation_mul`, `leviAssociationEquivalence` and
  `representationAssociationReflexivity`, `...Symmetry`, `...Transitivity`
  (`AssociationLawsProof`);
- `conjugatesLevi_inv`, `conjugatesLevi_mul` (product `v * w` from
  `hw : ConjugatesLevi B C w` and `hv : ConjugatesLevi C D v`) and
  `conjugatesLevi_weyl_mem` (`MinimalConjugatingCosetsProof`).

## Equal block counts

`ConjugatesLevi.blockIndex_eq` shows that a conjugating permutation `w` sends
two coordinates in a common block of `B` to coordinates in a common block of
`C`. The transposition of the two coordinates lies in the block Weyl group of
`B`; `conjugatesLevi_weyl_mem` puts its conjugate `w (a b) w⁻¹`, which is the
transposition of `w a` and `w b` (`Equiv.swap_apply_apply`), in the block Weyl
group of `C`. Evaluating at `w a` gives the claim.

`ConjugatesLevi.length_le` maps each block `i` of `B` to the block of `C`
containing the image under `w` of the first coordinate of block `i`. If two
blocks have the same image, then `blockIndex_eq` applied to `w⁻¹` (via
`conjugatesLevi_inv`) puts their first coordinates in a common block of `B`, and
`blockIndex_index` (from `WeylDefinitions`) shows that the blocks are equal.
This injection gives `B.length ≤ C.length`. The equality is reused from
`TotalConjugatingCount.length_eq` in
[`TotalConjugatingCountProof`](TotalConjugatingCountProof.md);
`LevisAssociated.length_eq` is its existential form.

## Transport

- `transport_one`: transporting along `1` (with `conjugatesLevi_one B`) gives
  back the same representation, by `leviConjugation_one`.
- `transport_inv`: for `hw : ConjugatesLevi B C w`, transporting a `C`-Levi
  representation `σ` back along `w⁻¹` (with `conjugatesLevi_inv hw`) is `σ`
  restricted along the forward Levi equivalence `leviConjugation B C w hw`, by
  `leviConjugation_inv_symm`.
- `transport_mul`: for `hw : ConjugatesLevi B C w` and `hv : ConjugatesLevi C D v`,
  transporting along `v * w` (with `conjugatesLevi_mul hw hv`) is transporting
  along `w` and then along `v`. Both sides are checked on each Levi element,
  using `leviConjugation_mul` and `MulEquiv.symm_trans_apply`.
- `transportEquiv`: an intertwining equivalence `ρ ≃ σ` of `B`-Levi
  representations is an intertwining equivalence of their transports along any
  conjugating `w`, with the same underlying linear equivalence.

## Association laws in dot notation

- `LevisAssociated.refl`, `.symm`, `.trans` are the three components of the
  published `leviAssociationEquivalence`.
- `RepresentationsAssociated.refl`, `.symm`, `.trans` are the published
  `representationAssociationReflexivity`, `representationAssociationSymmetry`
  and `representationAssociationTransitivity`, specialized to implicit block
  shapes and representations. The carrier universes `uV`, `uW`, `uX` are
  independent.
