# Images of parabolic subgroups in a quotient by the centre

This module is a helper for the proof of
`AdjointParabolicCorrespondenceStatement` (Conrad, *Reductive group schemes*
(2014), Exercise 5.5.8). It proves clause 2 of that statement: every relative
parabolic `P` of a reductive `G` is the full inverse image of a relative
parabolic of `G^ad`. It also proves that `G^ad` is affine over the base. Both
results assume `RelativeCentralMultiplicativeTypeQuotientStatement` (the affine
fppf quotient by a closed central subgroup of multiplicative type, isolated
from the proof of Conrad's Lemma 3.3.2) as an explicit hypothesis `hquot`.
Namespace `Langlands.GroupScheme.AdjointParabolicCorrespondence`.

## `isCentral_kernelι_baseChange`

Hypotheses: `b : S' ⟶ S`, `q : G ⟶ Q` over `S`, and `IsCentral (kernelι q)`.

Conclusion: `IsCentral (kernelι ((GroupScheme.baseChange b).map q))`.

Proof. Centrality is `range ≤ center` (`isCentral_iff_range_le_center`). The
kernel of a base change has the base-changed range
(`kernel_range_baseChange`, `range_baseChangeHom`), and `IsCentral.baseChange`
preserves centrality.

## `isParabolicSubgroup_image_of_centralKernel` (over a field)

Hypotheses: `k` is a field. Over `Spec k`:

- `G` is smooth and affine, and `A` is affine.
- `q : G ⟶ A` is flat and locally of finite presentation, with
  `IsCentral (kernelι q)`.
- `i : P ⟶ G` is a parabolic subgroup (`IsParabolicSubgroup i`).
- `p : P ⟶ I` is surjective.
- `j : I ⟶ A` is a closed subgroup and `I` is smooth.
- `i ≫ q = p ≫ j`.

Conclusion: `IsParabolicSubgroup j`.

This is the central-kernel analogue of the published
`UnipotentQuotientParabolics.isParabolicSubgroup_image`, and the proof follows
the same pattern.

Proof. `j` is closed and `I` is smooth by hypothesis. It remains to find a
Borel subgroup of `A` over `k̄` contained in `I_{k̄}`. Base change everything to
the algebraic closure `k̄` (`toAlgebraicClosure`). Flatness, local finite
presentation and centrality of the kernel are preserved
(`MorphismProperty.overPullbackMap`, `isCentral_kernelι_baseChange`). Since
`i` is parabolic, `P_{k̄}` contains a Borel subgroup `jB : B ⟶ G_{k̄}`, with
`a : B ⟶ P_{k̄}` and `a ≫ i_{k̄} = jB` (`IsParabolicSubgroup.exists_isBorelSubgroup`).
Let `J` be the image of `a ≫ p_{k̄}`, with `d : B ⟶ J` surjective and a closed
subgroup `c : J ⟶ I_{k̄}` (`HomImage.exists_image`). Then `J` is smooth and
connected, `c ≫ j_{k̄}` is a closed subgroup of `A_{k̄}`, and
`jB ≫ q_{k̄} = d ≫ (c ≫ j_{k̄})`. The published
`CentralIsogenyBorelPreimage.isBorelSubgroup_image` then says that `c ≫ j_{k̄}`
is a Borel subgroup of `A_{k̄}`. It factors through `j_{k̄}` via `c`.

## `quasiCompact_of_isAffineHom`

A homomorphism `q : G ⟶ Q` between groups that are affine over `S` is
quasi-compact. Proof: `q ≫ (Q → S)` is affine, so `q` is affine
(`IsAffineHom.of_comp`) and therefore quasi-compact.

## `isIso_comparison`

Hypotheses: `q : G ⟶ Q` and `r : G ⟶ R` are both fppf quotients of `G` by the
same subgroup functor `F` (`RelativeRoot.IsFppfQuotient F`), and `q` is
quasi-compact.

Conclusion: the published comparison homomorphism
`FppfQuotientComparison.hom hq hr : Q ⟶ R` is an isomorphism of underlying
schemes.

Proof. The comparison map is the `quotientSubgroupHom` of the identity
subgroup `𝟙 G` (`quotientSubgroupHom_unique`). The kernels of `q` and `r` have
the same range `F`, so all hypotheses of `quotientSubgroupHom_isPullback` hold.
The resulting square says that the comparison map pulls back along `r` to
`𝟙 G`. Since `r` is surjective, flat and locally of finite presentation,
isomorphisms descend along it (`MorphismProperty.of_isPullback_of_descendsAlong`).
Only the source quotient `q` has to be quasi-compact, because
`quotientSubgroupHom` is built by fpqc descent along it.

## `isAffineHom_of_isFppfQuotient_center`

Hypotheses: `hquot : RelativeCentralMultiplicativeTypeQuotientStatement`, `G`
reductive, and `q : G ⟶ Gad` an fppf quotient by `center G`.

Conclusion: `IsAffineHom Gad.X.hom`.

Proof. `reductiveRelativeCenter` gives a closed central subgroup `z : Z ⟶ G` of
multiplicative type with `range z = center G`. Applying `hquot` to `G` and `z`
gives an fppf quotient `q₀ : G ⟶ Q₀` by `center G` with `Q₀` affine over `S`.
Then `q₀` is quasi-compact (`quasiCompact_of_isAffineHom`), so
`isIso_comparison` makes `Q₀ → Gad` an isomorphism over `S`. Hence
`Gad → S` equals the inverse of this isomorphism followed by `Q₀ → S`, which is
affine.

## `exists_parabolic_image` (clause 2)

Hypotheses: `hquot : RelativeCentralMultiplicativeTypeQuotientStatement`, `G`
reductive over `S`, `q : G ⟶ Gad` an fppf quotient by `center G`, and
`i : P ⟶ G` a relative parabolic subgroup.

Conclusion: there are `P'` and `i' : P' ⟶ Gad` with
`IsRelativeParabolicSubgroup i'` and
`(SubgroupFunctor.range i').comap q = SubgroupFunctor.range i`.

Proof.

1. `Gad` is affine over `S` (`isAffineHom_of_isFppfQuotient_center`), so `q`
   is quasi-compact. `i` is a closed subgroup (`relativeParabolicClosed`), and
   `center G ≤ range i` (`IsRelativeParabolicSubgroup.center_le_range`, module
   `Reductive/ParabolicContainsCenter`).
2. Take the centre `z : Z ⟶ G` from `reductiveRelativeCenter`. Since
   `range z = center G ≤ range i`, `z` factors as `zP ≫ i`
   (`SubgroupFunctor.factorOfRangeLE`). `zP` is closed
   (`IsClosedSubgroup.of_comp`) and central (`IsCentral.of_comp`), and `Z` is of
   multiplicative type.
3. `P` is smooth and affine with connected geometric fibres
   (`IsRelativeParabolicSubgroup.connectedSpace_geometricFiber`). So `hquot`
   applied to `P` and `zP` gives an fppf quotient `π : P ⟶ Q` by `range zP`,
   with `Q` affine over `S`. Then `π` is quasi-compact, and `Q` is smooth by
   `smooth_target_of_surjective_flat_hom_overBase`.
4. The kernel conditions of the published `SubgroupFunctor.quotientSubgroupHom`
   hold: `range (kernelι π) = range zP` is exactly the inverse image under `i`
   of `range (kernelι q) = center G = range z` (`i` is a monomorphism and
   `zP ≫ i = z`), and `range (kernelι q) ≤ range i` by step 1. Let
   `i' := quotientSubgroupHom i q π _ : Q ⟶ Gad`. It is a monomorphism
   (`quotientSubgroupHom_mono`) and a closed subgroup
   (`quotientSubgroupHom_isClosedSubgroup`). It satisfies `i ≫ q = π ≫ i'`
   (`quotientSubgroupHom_square`) and `(range i').comap q = range i`
   (`quotientSubgroupHom_comap_range`).
5. Fibres. Fix `s : S` and base change along `Spec κ(s) ⟶ S`. `G_s` is smooth,
   affine and connected reductive (`IsReductive.isConnectedReductive_residueFiber`).
   `Gad_s` is affine, `Q_s` is smooth, `q_s` is flat and locally of finite
   presentation with central kernel, `π_s` is surjective, `i_s` is parabolic,
   and `i'_s` is a closed subgroup (`IsClosedSubgroup.baseChange`). The square
   base-changes to `i_s ≫ q_s = π_s ≫ i'_s`. So
   `isParabolicSubgroup_image_of_centralKernel` shows that `i'_s` is parabolic.

Together with smoothness and affineness of `Q` and monicity of `i'`, this is
`IsRelativeParabolicSubgroup i'`.
