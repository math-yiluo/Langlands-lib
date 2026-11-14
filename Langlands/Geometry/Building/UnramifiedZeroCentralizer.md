# Zero data for split-torus centralizers and unramified comparison

This module constructs compatible upstairs zero data and proves the
algebraic centralizer comparisons used in unramified zero descent. Its main
construction, `UnramifiedZeroDatum.ofCentralizer`, is defined for a
nonarchimedean local field `F`, groups `G`, `M` over
`K = UnramifiedClosure F`, supplied zero data `E` on `G` and `EM` on `M`,
a split-subtorus inclusion `a : A.toGrp ⟶ G`, and a representation
`j : M ⟶ G` of its centralizer. It takes the torus and splitting field of
`EM` and the derived cover of `E` to form another zero datum on `G`.

The supporting torus lemma proves that a maximally split maximal torus of
this centralizer remains maximal and maximally split in `G`. The original
split torus is central in its centralizer, so it factors through each of
its maximal tori and maximal split tori. Any larger ambient torus still
centralizes the original split torus and therefore factors through `M`.
This reduces both maximality assertions to their counterparts in `M`.

Two preliminary lemmas apply beyond the local-field setting:

- `map_simplyConnectedImage_le_of_hom` proves functoriality of the simply
  connected image under any homomorphism of group schemes over a field,
  with supplied derived covers. It maps the derived subgroups, then uses
  the published homomorphism lifting theorem through the target cover.
- `rationalExtend_mem_simplyConnectedImage` proves preservation of the
  simply connected image under any field extension. Base change produces
  one cover upstairs, and cover independence compares it with the supplied
  cover.

The compatible datum and published upstairs datum independence give
`UnramifiedZeroDatum.map_zeroPoints_centralizer_le`: the image of
`EM.zeroPoints` under `j` lies in `E.zeroPoints`. The simply connected
factor uses functoriality; the torus factor is shared by the compatible
data.

The stronger comparison is
`UnramifiedZeroDatum.zeroPoints_comap_centralizer_inf_characterValuationKernel`:

`E.zeroPoints.comap (rationalPoints.map j) ⊓ characterValuationKernel v M = EM.zeroPoints`,

where `v` is the fixed-field valuation of `K`. The intersection with the
centralizer's character-valuation kernel is part of the assertion. The
proof rewrites the ambient zero group using the compatible datum, expresses
membership as a product of a simply connected image point and a torus
Iwahori point, and removes the torus factor. The remaining point lies in
the centralizer's character kernel and in the ambient cover image. The
published cover-preimage, induced-cocenter and torus Iwahori results put it
in the centralizer zero subgroup. Restoring the torus factor proves the
upper inclusion. The lower inclusion combines the preceding image lemma
with the centralizer zero subgroup's containment in its character kernel.

For every downstairs `Z0 : ZeroSubgroupDatum i j` on a group `G` over `F`
and every upstairs `E` on `G_K`,
`ZeroSubgroupDatum.zeroSubgroup_le_comap_unramifiedZeroPoints` proves

`Z0.zeroSubgroup ≤ E.zeroPoints.comap (rationalExtend F K G)`.

The simply connected part extends by the preliminary scalar-extension
lemma. The centralizer zero part extends by naturality and the upstairs
centralizer inclusion. The final theorem,
`ZeroSubgroupDatum.comap_unramifiedZeroPoints_inf_centralizerNormKernel`,
restricts that preimage to the downstairs centralizer and intersects with
`Plancherel.rationalCommonNormKernel Z`; the result is exactly
`Z0.centralizerZero`. It uses character-kernel descent and the upstairs
intersection identity.

These conclusions require no building data or unramified zero-descent
premise. They supply the lower inclusion of clause 3 of
`UnramifiedZeroDescentStatement` and the equality on norm-one points of
the minimal Levi. The upper inclusion for arbitrary rational points is
still outside this module.

The construction and comparisons are derived from the actual subgroup,
cover and norm definitions and published Library results. Their source
context is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 2.6.23, Lemma 2.6.24, Remark 2.6.26 and Corollary 2.6.28,
printed pp. 104–105 / PDF pp. 135–136, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The proof of the final
norm-kernel identity is the composition described above; this module does
not claim a proof of the full descent target.
