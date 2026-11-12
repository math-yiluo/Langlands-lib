# Normality of `G(F)^0` and of `Z(F)^0` from commutators in `G(F)^♮`

This module proves two normality results without any hypothesis. The first is that
`G(F)^0` is normal in `G(F)`, for every zero datum. The second is that, for actual
`ParahoricBuildingData`, `Z(F)^0` is normal in the full normalizer `N(F)`. Previously the
Library obtained the second only from KP Lemma 2.6.24, independence of the defining choices of
`Z(K)^0` (`UnramifiedZeroPointsIndependenceStatement`), through
`ParahoricBuildingData.normalizerZero_normal`. The route here does not use that independence.

## Declarations

* `commutator_mem_simplyConnectedImage h x y`. For a field `k`, a simply connected derived
  cover `h : IsSimplyConnectedDerivedCover d π` and `x y ∈ G(k)`, the commutator
  `x * y * x⁻¹ * y⁻¹` lies in `simplyConnectedImage d π`, that is, in `G(k)^♮`. This is the
  case `T = Spec k` of `IsSimplyConnectedDerivedCover.exists_comp_eq_commutator`
  (module `Langlands.GroupScheme.SimplyConnected.CommutatorCoverImage`).
* `normal_of_simplyConnectedImage_le h hH`. Every subgroup `H` of `G(k)` containing `G(k)^♮`
  is normal: for `x ∈ H` and `g ∈ G(k)`, `g x g⁻¹ = (g x g⁻¹ x⁻¹) · x` is a product of a
  commutator and an element of `H`.
* `ZeroSubgroupDatum.normal_zeroSubgroup E`. For every zero datum `E` over a nonarchimedean
  local field, `E.zeroSubgroup = G(F)^♮ · Z(F)^0` is normal in `G(F)`. It contains `G(F)^♮`
  (`simplyConnectedImage_le_zeroSubgroup`), and the datum carries the simply connected derived
  cover `E.isSimplyConnectedDerivedCover`.
* `ParahoricBuildingData.normal_zeroSubgroup P`. The same for `P.zeroSubgroup`, which is by
  definition `P.zeroDatum.zeroSubgroup`.
* `ParahoricBuildingData.normal_normalizerZero P`. `P.normalizerZero`, the image of `Z(F)^0` in
  `N(F)`, is normal in `N(F)`. This applies the published
  `normalizerZero_normal_of_zeroSubgroup_normal` (module `NormalizerZeroNormality`) to the
  normality of `G(F)^0` above and to the published cover comparison
  `ZeroSubgroupDatum.coverImageCentralizerNormKernel` (module
  `ChamberConjugateIntersectionProof`, the containment `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` from the
  proof of KP Corollary 2.6.28). That published theorem writes `Z(F)^0` as the intersection of
  `N(F) ∩ G(F)^0` with the kernel of the action of `N(F)` on the apartment. Both are normal in
  `N(F)`.

The names `normal_zeroSubgroup` and `normal_normalizerZero` are chosen so that they do not
clash with the published conditional `ParahoricBuildingData.zeroSubgroup_normal` and
`ParahoricBuildingData.normalizerZero_normal`. Those take Fact 2.6.22 and KP Lemma 2.6.24 as
hypotheses.

## Provenance

The normality of `G(k)^0` is part of KP Lemma 2.6.24 (Kaletha–Prasad, *Bruhat–Tits theory: a
new approach*, printed p. 104, book PDF p. 135, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`). KP deduce it from the normality of `G(k)^♮` and
the independence of the choices of `T` and `M_0`. The proof here is different and needs no
independence: `G(k)^0` contains `G(k)^♮`, and `G(k)^♮` contains every commutator. The normality
of `Z(F)^0` in `N(F)` is the internal consequence described above. It is also a consequence of
KP Lemma 2.6.24 (conjugation by `n ∈ N(F)` carries the data defining `Z(F)^0` to other valid
data). These results are internal derived content assembled from published Library theorems.
They do not prove the independence statement `UnramifiedZeroPointsIndependenceStatement` itself.
