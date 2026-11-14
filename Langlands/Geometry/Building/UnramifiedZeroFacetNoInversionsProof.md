# The zero group acts without inversions over the maximal unramified field

Author: Worker 241. The quotient-to-normalizer reduction follows the draft
supplied by Worker 82 in Task 6612.

`Langlands.Geometry.Building.MaximalUnramified.zeroFacetNoInversions`
proves exactly the unchanged published proposition
`Langlands.Geometry.Building.MaximalUnramified.ZeroFacetNoInversionsStatement.{u}`,
at arbitrary universe `u`, without additional premises.

For every original nonarchimedean local field `F` in either characteristic, put
`K = Langlands.LocalGalois.Separable.inertiaFixedField F`. The theorem uses every
affine `K`-group `H`, every supplied `C : MaximalUnramified.BuildingData F H`,
every `E : UnramifiedZeroDatum F H`, all apartment points `x, y`, and every
`g ∈ H(K)`. If `y` belongs to the affine-root facet of `x`, `g ∈ E.zeroPoints`,
and `g • C.apartmentMap x = C.apartmentMap y`, its conclusion is `y = x`.
The apartment, affine roots, zero subgroup and rational-point action are those
of the published statement.

## Implemented proof

1. Expand the equality in the actual reduced-building quotient.
   `ApartmentQuotient.mk_eq_mk_iff` gives an actual normalizer point `n`
   with `n • x = y` and `g⁻¹ n ∈ C.sharpFixer {x}`.
2. The unconditional theorem `E.sharpFixer_le_zeroPoints C {x}` places
   `g⁻¹ n` in `E.zeroPoints`. Since `g` also belongs to this subgroup,
   multiplication gives `n ∈ E.zeroPoints`.
3. Apply
   `E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints` to the proved theorem
   `MaximalUnramified.simplyConnectedNormalizerAffineWeyl`. This puts the
   original affine action of `n` in
   `AffineRootSystem.affineWeylGroup C.affineRoots`; no normalizer-image
   assertion remains a premise.
4. `C.hasOppositeFactorPairs` and
   `C.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs`
   prove local finiteness of the reflection arrangement of the actual roots.
   Write `w` for the affine Weyl element just obtained. The original
   normalizer action gives `w x = y`, while facet membership gives
   `facetRel C.affineRoots x (w x)`.
5. `AffineRootSystem.eq_of_facetRel_apply` shows `w x = x`. Rewriting with
   `w x = y` proves the conclusion.

The published consequence
`ZeroFacetNoInversionsStatement.mem_pointwiseFixer_of_isFacet` therefore applies
without a remaining statement premise: an element of `E.zeroPoints` mapping
any facet of the reduced building into itself fixes it pointwise. The proof
covers all facets and rank zero, and requires neither descent of `H` to `F`
nor a separately supplied Tits system.

## Provenance and independence

This is an internal composition of the named Library theorems. The unchanged
target Markdown records the comparison with Kaletha–Prasad 4.1.12(1),
Proposition 7.6.4(1) and the quotient of Remark 7.6.5. The implemented proof uses
the quotient relation and the affine reflection arrangement directly.

The simply connected normalizer theorem is proved from
`quasiSplitSimplyConnectedRootGeneration` by
`simplyConnectedNormalizerAffineWeyl_of_quasiSplitRootGeneration`. That route
establishes quasi-splitness over the actual Henselian inertia fixed field and
uses algebraic root generation and integer-valued normalizer generation on
the same supplied datum. The sharp-fixer inclusion uses lifting of relative
root groups through the simply connected derived cover. The zero-normalizer
comparison uses maximal split torus conjugacy, torus norm character kernels
and the derived-cover apartment comparison. The last step is the geometric
affine Weyl facet-fixing theorem.

Neither this proof nor the published proofs it uses depend on
`UnramifiedZeroDescentStatement`, directly or transitively, or on integral
models constructed using that statement. No integral model is supplied as a
premise. The dependency check includes the proof of the simply connected
normalizer theorem.
