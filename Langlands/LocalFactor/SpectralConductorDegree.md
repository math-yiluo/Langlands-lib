# The residue degree of an intermediate field in the induction identity

Worker 4803 wrote this supporting module of
`SpectralConductor.spectralConductorRankOneReduction`.

## Results

- `relIndex_sup_normal`: for subgroups `H, N` with `N` normal,
  `[H ⊔ N : H] = [N : H ∩ N]` (Mathlib's `relIndex`). Proof: the inclusion of `N`
  induces a bijection of left coset spaces. Injectivity is the definition of the
  relation. For surjectivity, every element of `H ⊔ N` is `z y` with `z ∈ N`, `y ∈ H`
  (`Subgroup.mem_sup_of_normal_left`). Mathlib's `relIndex_sup_right` is the other
  second-isomorphism index formula, `[H ⊔ N : N] = [H : H ∩ N]`.
- Normalization at `L` (`ord_mul_log`): for `w ∈ W_L`,
  `ord_L(rec_L(w)) · log q_L = deg(w) · log q_F`. This is the
  `NormalizationRelation` part of `NormalizedReciprocity` applied at `L`, as in the
  Library's `character_eq_norm_exp`: `|rec_L(w)|_L = q_F^{-deg w}` and
  `|x|_L = q_L^{-ord x}`.
- `uniformizerWeil e L` is an element of `W_L` whose reciprocity image is the chosen
  uniformizer of `L` (reciprocity is surjective). `residueDegreeL e L` is its base
  degree `f`. Then `log q_L = f log q_F` (`log_residueCardinality`), `f > 0`, and every
  `w ∈ W_L` has degree `ord_L(rec_L(w)) · f` (`degree_eq_ord_mul`).
- `map_degree_weilSubgroup`: the base degrees of `W_L` are exactly the multiples of `f`.
- `index_weilSubgroup`: `[W_F : W_L] = [I_F : W_L ∩ I_F] · f`. Proof:
  `[W_F : W_L] = [W_L ⊔ I_F : W_L] · [W_F : W_L ⊔ I_F]`. The first factor is
  `[I_F : W_L ∩ I_F]` by `relIndex_sup_normal`. The second is the index of `fℤ` in `ℤ`:
  `W_L ⊔ I_F` is the preimage of the degrees of `W_L` (`Subgroup.comap_map_eq`; Weil
  inertia is the kernel of the degree), the degree is surjective
  (`localDegree_surjective`), and `Int.index_zmultiples`.
- `relIndex_localInertia`: `[I_F : W_L ∩ I_F] = [I(M/F) : I(M/L)]`, since
  `weilInertiaRestriction F M` is surjective and `W_L ∩ I_F` is the preimage of the
  elements fixing `L` (`mem_weilSubgroup_iff`). `card_inertiaL_mul_index` then gives
  `|I(M/L)| · [I(M/F) : I(M/L)] = |I(M/F)|`.
- `card_cosets_nestedL`: the number of right cosets of `W_L` in the base Weil group is
  `[W_F : W_L]`.
- `residueCardinality_base`: the bottom field has the residue cardinality of `F`. The
  proof is that of the Library's `Correspondence.baseResidueCardinality_eq`.
- `inductionFactor_mul_logCardinality`:
  `#cosets · |I(M/L)| / |I(M/F)| · log q_F = log q_L`.

## Sources

The identity says that the factor of the induction identity is the residue degree
`f_{L/F}` and that `q_L = q_F^{f_{L/F}}` (Serre, *Local Fields*, I §4 and VI §2,
Proposition 4, printed pp. 101–102). This proof uses only the supplied geometric
normalization of reciprocity and group indices, not ramification indices.
