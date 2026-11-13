# Common-closure reciprocity families along an isomorphism of p-adic fields

Worker 5130, Task 5230. Internal derived infrastructure; no external source beyond
the published Library results named below.

For `g : F ≃ₐ[ℚ_p] E` and a reciprocity family `eE` on the common closure of `E`,
`transportFamily F E g eE` is the family on `F` whose component at `L` is

`Ab(W_F(L)) ≅ Ab(W_E(σ(L))) → σ(L)ˣ ≅ Lˣ`.

The first map is `abelianizationCongr` of `subgroupWeilEquiv L` inverted, the second
is `eE σ(L)`, and the third is the inverse of `unitsEquiv L`, the Library's
`ConductorTransport.unitsEquiv` for `fieldEquiv L`. A local instance gives every
`asPadicField` its canonical topology.

* `transportFamily_normRelation`: the norm relation is transported. Its inputs are
  `abelianizationCongr_symm_weilAbelianInclusion` (the abelianized inclusions commute
  with the subgroup isomorphisms, checked on generators) and `unitsEquiv_unitsNorm`
  (the field norm commutes with `L ≅ σ(L)`). The latter follows from Mathlib's
  `Algebra.norm_eq_of_equiv_equiv` and `fieldEquiv_algebraMap_comp`.
* `transportFamily_normalizationRelation`: the geometric normalization is
  transported. It uses `CanonicalTransport.normalizedAbs_map` for `fieldEquiv L`,
  `weilDegree_abelianizationCongr_symm` (base-field degrees agree, from
  `localDegree_weilEquiv`) and `CanonicalTransport.residueCardinality_eq`.
* `transportFamily_normalizedReciprocity`: if `eE` is normalized, so is its transport.
  A normalized family `e₀` on `F` exists by `commonClosureReciprocityExistence`.
  `ReciprocitySystemUniqueness.eq_of_norm_normalization`, applied with
  `weilGaloisAbelianProjection_injective`, shows that the transport equals `e₀`.
