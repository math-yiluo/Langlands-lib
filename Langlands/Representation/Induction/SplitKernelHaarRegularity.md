# Open kernels for the actual split-kernel Haar character

This internally derived result identifies the exact character used by the
split-kernel quotient integral with a ratio of the existing ambient normalizer
Haar characters. It proves an open kernel for that character and its constant
image in any commutative complex coefficient algebra. Group, section group,
coefficient ring and representation carrier have independent universes.

The construction starts with group homomorphisms `r : G →* L` and
`s : L →* G`, a subgroup `H` of `G`, and membership `s(l) ∈ H` for every
`l`. No retraction identity is required for this character calculation.
The section normalizes the normal subgroup `N = ker r` and the ambient
intersection `Z = N ⊓ H`. The two homomorphisms
`splitKernelNormalizerSection` and `splitKernelIntersectionNormalizerSection`
send `l` to that same element `s(l)` in the corresponding normalizer.
`splitKernelIntersectionAmbientEquiv` identifies `H.comap N.subtype` with
`Z` by preserving its original value in `G`.

For the Haar identity, `G` is a locally compact topological group, the kernel
has its locally compact structure and Borel measurable structure, the nested
intersection has a Borel measurable structure, and both `N` and `H` are
closed. Write `δN(l)` and `δZ(l)` for the closed normalizer Haar characters
evaluated at the section value. Then
`splitKernelHaarRatio_eq_normalizerCharacters` proves the equality of
homomorphisms

```text
splitKernelHaarRatio r s H hsH hH = δN / δZ.
```

The implemented proof transports the actual inverse conjugation on the kernel
and its nested intersection through the identity and the intersection
equivalence. The published
`CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter` identifies
their Haar factors with `δN(l)⁻¹` and `δZ(l)⁻¹`. The ratio already used by
the integral is the intersection factor divided by the kernel factor, hence
`δN(l) / δZ(l)`. This retains the actual inverse-conjugation orientation and
allows the supplied Borel structures; it does not assume a modulus identity.

For openness, assume additionally that `G` is nonarchimedean, that `L` is a
topological group, and that `s` is continuous. The existing normalizer Haar
characters have open kernels. Their pullbacks through the continuous section
normalizer maps therefore have open kernels in `L`. The intersection of these
two kernels is open and lies in the ratio's kernel.
`isOpen_ker_splitKernelHaarRatio` concludes by openness of a subgroup
containing an open subgroup.

For every commutative complex algebra `R`,
`isOpen_ker_splitKernelHaarCoefficientCharacter` applies to the exact character

```text
(Units.map (algebraMap ℂ R).toMonoidHom).comp
  (Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH)).
```

Its kernel contains the positive ratio's open kernel. No topology on `R` or
injectivity of `algebraMap` is required.
`splitKernelHaarSmoothCharacter` bundles this homomorphism with the proved
open-kernel property. The smoothness equivalence is an application of the
published `isSmooth_twist_iff`. For Noetherian `R`, the admissibility
equivalence is an application of the published native
`isAdmissible_twist_iff`; it retains native `R`-module finiteness.

These are internal consequences of the existing split-kernel character and
normalizer Haar theory, rather than statements attributed verbatim to an
external source. They supply scalar-twist regularity only. Actual rational
orbit identifications, compatible quotient-measure existence, geometric
filtration and the main universal-family fixed-module finiteness proof remain
separate obligations.
