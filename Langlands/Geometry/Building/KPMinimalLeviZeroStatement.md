# Zero subgroups of actual minimal Levi subgroups

This module states the local-field comparisons from KP Lemma 2.6.27 and
Corollary 2.6.28 on the already supplied `ZeroSubgroupDatum`. It does not prove
their reverse inclusions. It also names the smaller cover-image containment
used in the source proof and proves that it follows from the second comparison.

All declarations are at arbitrary universe `u`, for every nonarchimedean local
field `F` of either characteristic and every actual `E : ZeroSubgroupDatum i j`.
Here `i : S → G` is a maximal split torus and `j : Z → G` represents its
centralizer. Thus `Z` is the actual minimal Levi subgroup. Those properties
come from `E`; they are not new assumptions or newly chosen subgroup schemes.

## Exact statements

`E.CentralizerZeroNormKernelStatement` is the local-field consequence of
Lemma 2.6.27:

```text
IsSimplyConnected G →
  E.centralizerZero = Plancherel.rationalCommonNormKernel Z.
```

This states `Z(F)^0 = Z(F)^1` when the ambient group `G` is simply connected.
It makes no such equality assertion for a general connected reductive ambient
group. The source first proves the equality over its maximal unramified
extension `K` and then descends to `F`; the present target states only the
result over `F`.

`E.CentralizerZeroIntersectionStatement` is the second assertion of
Corollary 2.6.28:

```text
E.zeroSubgroup.comap (rationalPoints.map j) ⊓
  Plancherel.rationalCommonNormKernel Z = E.centralizerZero.
```

The comap expresses membership in `G(F)^0` after applying the actual inclusion
`j`. Its intersection with `Z(F)^1` is asserted to equal `Z(F)^0`.
`E.MinimalLeviZeroComparisonStatement` is the conjunction of these two targets.
Neither target is made a field of `E` or a premise of the final parahoric
intersection target.

`E.CoverImageCentralizerNormKernelStatement` is the weaker containment

```text
E.simplyConnectedImage.comap (rationalPoints.map j) ⊓
  Plancherel.rationalCommonNormKernel Z ≤ E.centralizerZero.
```

It restricts to `G(F)^♮` rather than all of `G(F)^0`. This is the local-field
containment needed for a sharp fixer whose inclusion in the actual derived-cover
image and whose boundedness have been proved separately.

All zero subgroups retain the published definitions: `centralizerZero` is
the scalar-extension comap of the supplied `UnramifiedZeroDatum.zeroPoints`,
and `zeroSubgroup` is the join of the actual derived-cover image and the
mapped centralizer-zero subgroup. No choice of splitting field, torus or cover
is replaced. The statements quantify over every supplied valid datum; the
choice comparisons required by a proof remain obligations.

## Sources and provenance

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
The original passages read directly are Definition 2.6.20 and
Definition 2.6.23, printed page 104 / PDF page 135, Lemma 2.6.27 and its proof,
printed page 105 / PDF page 136, and Corollary 2.6.28 with its proof,
printed pages 105–106 / PDF pages 136–137.

Lemma 2.6.27 uses induced maximal tori and the induced derived and quotient
tori over `K`. It applies Lemma 2.5.18 to identify the quotient torus's zero
and norm-one subgroups, lifts through the torus map by Lemma 2.5.20, and
puts the remaining derived element into the zero subgroup.
Corollary 2.6.28 pulls the minimal Levi back to the simply connected cover.
Its finite kernel identifies the inverse image of the norm-one subgroup;
Lemma 2.6.27 and compatibility of zero subgroups with that map give the
cover-image containment. These describe the source route, not implemented
proofs of the targets in this module.

The local cover-image target is a derived restriction of Corollary 2.6.28.
The source proof establishes the corresponding containment over `K`, while
the full local-field intersection comparison immediately implies the target
on `F`-points.

The 1 November 2024 corrections, registered as
`kaletha-prasad-2024-corrections`, PDF pages 24–25, change the sign of the
character-valuation maps, add the Henselian and perfect-residue-field
standing assumptions before Definition 2.6.20, and specify the base field
in Definition 2.6.23. Nonarchimedean local fields satisfy those field
assumptions, and the sign changes do not change the norm kernels.
No project errata file for either registered source was found.

## Implemented supporting proofs and remaining work

`centralizerZero_le_zeroSubgroup_comap_inf_normKernel` proves the immediate
inclusion into the displayed intersection. The first component is the
existing mapped-centralizer-zero inclusion into `E.zeroSubgroup`; the second
is `E.centralizerZero_le_rationalCommonNormKernel`.

`coverImageCentralizerNormKernel_of_intersection` assumes the full intersection
target, includes `E.simplyConnectedImage` into `E.zeroSubgroup`, and rewrites
by the assumed equality. It proves only this implication. The three named
comparison propositions remain unproved.

Proving the targets still requires the actual induced-torus, quotient,
norm-image surjectivity and simply connected cover comparisons used in the
source route, or another complete argument. This module asserts neither their
existence nor the existence of zero-subgroup data. It supplies no sharp-fixer
boundedness result and no final proof of KP Lemma 7.4.3.
