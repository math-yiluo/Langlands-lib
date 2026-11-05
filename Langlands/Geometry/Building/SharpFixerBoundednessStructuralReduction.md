# Singleton sharp-fixer boundedness from the remaining structural statements

This derived, internal unit proves that four Library statements, which are
not yet proved, imply the exact target
`ValuationBuildingData.SharpFixerBoundednessStatement` (Kaletha–Prasad
Corollary 7.3.14 for a single point) for every actual
`B : ValuationBuildingData G` over a nonarchimedean local field `F : Type u`.
The four statements are explicit hypotheses:

- `RootRankOneFactorizationStatement` (module
  `Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement`):
  every nonidentity point of a relative root group has an opposite factor
  pair, the conclusion of Kaletha–Prasad Proposition 2.11.17;
- `BruhatTits.Cartan.ActualCentralizerStructureStatement`: the represented
  centralizer of a maximal split torus is connected reductive and the torus
  is its split component;
- `CentralQuotientReductiveStatement`: quotients of connected reductive groups
  by central subgroups are connected reductive;
- `AnisotropicCompactnessStatement`: for a connected reductive group over a
  nonarchimedean local field, the set of rational points is compact in the
  canonical topology if and only if the group is anisotropic (split rank
  zero), the locally compact consequence of Kaletha–Prasad Theorem 2.2.9
  (printed p. 71, PDF p. 102).

The first gives the cover of `PointSharpExchange`; the last three give
compactness of `Z(F)^1`. Once all four are proved in the Library, applying
`sharpFixerBoundednessStructuralReduction` to their proofs proves the target
with no hypothesis.

## Statements

- `ValuationBuildingData.centralizer_isCentral_maximalSplit`: for
  `B : ValuationBuildingData G`, the factorization `B.centralizer.s : S → Z`
  of `B.i` through the centralizer `j : Z → G` is central in `Z` and is a
  maximal split torus of `Z`.
- `ValuationBuildingData.isCompact_centralizerNormKernel`: assume
  `ActualCentralizerStructureStatement`, `CentralQuotientReductiveStatement`
  and `AnisotropicCompactnessStatement` at universe `u`. Then the rational
  common norm kernel `Z(F)^1 = rationalCommonNormKernel B.centralizer.Z` is
  compact in the canonical topology `rationalPointTopology F B.centralizer.Z.X`
  on `Z(F)`.
- `ValuationBuildingData.sharpFixerBoundedness_of_structure`: assume the four
  statements at universe `u`. Then `B.SharpFixerBoundednessStatement` holds:
  if `B.apartment` satisfies the apartment axioms
  `SatisfiesApartmentAxioms B.centralizer`, then for every point `x` of the
  apartment the sharp fixer `B.sharpFixer {x}` is algebraically bounded in
  `G(F)`.
- `SharpFixerBoundednessStructuralReductionStatement` is the Prop-valued entry
  definition: the four statements at universe `u` imply
  `B.SharpFixerBoundednessStatement` for every nonarchimedean local field
  `F : Type u`, every group scheme `G` over `F` with affine structure morphism
  and every `B : ValuationBuildingData G`. The theorem
  `sharpFixerBoundednessStructuralReduction` proves it.

## Proof

*Centrality and maximality.* The same argument as
`ParahoricBuildingData.centralizer_isCentral_maximalSplit` (module
`KPCentralizerNormKernelCompactness`), restated for `ValuationBuildingData`
because a `ValuationBuildingData` is not a `ParahoricBuildingData` (the latter
extends it by a `zeroDatum`). Centrality: the range of `s` lies in the
torus centralizer, because `s ≫ j = i` and `j` represents the centralizer of
`i` (`isCentral_of_range_le_torusCentralizer`). Maximality:
`IsMaximalSplitTorus.of_comp` along the closed subgroup `j`, using
`s ≫ j = i` and `B.isMaximalSplitTorus`.

*Compactness of `Z(F)^1`.* `ActualCentralizerStructureStatement`, applied to
`B.isConnectedReductive`, `B.isMaximalSplitTorus` and the fields of
`B.centralizer`, gives that `Z` is connected reductive. Together with
centrality and maximality of `s`,
`BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit`
(Worker 1450, module `KPCentralizerNormKernelCompactness`) gives compactness
from the other two statements.

*Boundedness.* `sharpFixerBoundedness_of_cover` (module
`SharpFixerBoundednessAssembly`) proves the target from two premises:
boundedness of `j(Z(F)^1)` in `G(F)`, and the cover
`G(F)^♯_x ⊆ X⁻ · X⁺ · (G(F)^♯_x ⊓ Stab_{N(F)}(x))` for every generic
cocharacter, under the apartment axioms. The first is
`isAlgebraicallyBounded_image_centralizerNormKernel_of_isCompact` applied to
the compactness above. The second is
`sharpFixer_subset_mul_sharpNormalizerStabilizer` (module
`PointSharpExchange`), with opposite factor pairs for `B.i` given by
`RootRankOneFactorizationStatement` applied to `B.isConnectedReductive`,
`B.S`, `B.i` and `B.isMaximalSplitTorus`; its third factor
`sharpNormalizerStabilizer x` is by definition the subgroup in the cover.

## Provenance

The unit assembles published or accepted Library results and has no direct
counterpart in the book. In Kaletha–Prasad, Corollary 7.3.14 (printed p. 251,
PDF p. 282) is proved from Proposition 7.3.12 (printed pp. 250–251, PDF
pp. 281–282) and the boundedness of the root groups and of `Z(F)^1`; the
existence of the elements `m(u)` used throughout Chapter 7 is Proposition
2.11.17 (printed p. 136, PDF p. 167). The four hypotheses isolate exactly the structural facts that the
Library does not yet prove; this unit asserts none of them.

## Sources

- Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
  Cambridge University Press, 2023 (source
  `kaletha-prasad-2023-bruhat-tits-new-approach`): Theorem 2.2.9,
  Proposition 2.11.17, Proposition 7.3.12 and Corollary 7.3.14.
