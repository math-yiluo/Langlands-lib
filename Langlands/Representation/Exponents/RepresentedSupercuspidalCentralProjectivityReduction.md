# Renard VI.3.6 from the structural statements

Author: Worker 1709. Module
`Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module derives the published proposition
`RepresentedSupercuspidalCentralProjectivityStatement` (Renard 2026, VI.3.6,
the Proposition after the Lemma, printed p.148 / PDF p.154, source
`renard-2026-representations-groupes-reductifs-padiques`) from five published
structural propositions, which are explicit premises. It does not prove the
target unconditionally.

## Results

- `finiteIndex_rationalCommonNormKernel_sup_center hLattice G hG`: for a
  connected reductive `G` over a nonarchimedean local field `k : Type u`, given
  `hLattice : Plancherel.RenardCartan.SplitComponentLatticeStatement.{u}`, the
  subgroup `Plancherel.rationalCommonNormKernel G ⊔ Subgroup.center (rationalPoints G)`
  has finite index. Proof: `GroupScheme.exists_isSplitComponent` gives a split
  component `i : A.toGrp ⟶ G`; the first conjunct of `hLattice` is
  `(splitValuationImage i).FiniteIndex`; `Plancherel.finite_rationalCentralQuotient`
  then makes `G(k) ⧸ (⁰G ⊔ image of A(k))` finite; the image of `A(k)` lies in the
  centre (`IsCentralSplitTorus.range_le_center`), so the larger subgroup
  `⁰G ⊔ Z(G(k))` has finite index too. This is the finiteness of
  `G / ⁰G Z(G)` used in VI.3.6, deduced as in Renard V.2.6, Proposition
  (printed p.108 / PDF p.114), from the finiteness of `G / ⁰G A_G`.
- `representedSupercuspidalCentralProjectivity_of_structure hPD hStandard hRoot hJoint hLattice`,
  with `hPD : ParabolicDynamicStatement.{u}`,
  `hStandard : StandardCocharacterStatement.{u}`,
  `hRoot : RelativeRootSystemStatement.{u}`,
  `hJoint : JointSpecialCompactBasisExistenceStatement.{u}` and `hLattice` as
  above, proves `RepresentedSupercuspidalCentralProjectivityStatement.{u, v}`.

## Proof of the second result

After introducing the data of the target, the rational points carry their
canonical topology, which is Hausdorff
(`AlgebraicGeometry.PointTopology.rationalPoint_t2Space`).

1. **Compact coefficients on `⁰G` (Renard VI.2.1, VI.3.2).** The target's
   supercuspidality hypothesis is, by definition, `IsSupercuspidal τ`, so
   `compactRestriction_of_isSupercuspidal hPD hStandard hRoot hJoint hG τ`
   gives `HasCompactNormKernelRestriction τ`, that is, compactly supported
   smooth-dual coefficients of `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) τ`.
2. **The open normal subgroup.** `H := Plancherel.rationalCommonNormOpenSubgroup G`
   is `⁰G` as an open subgroup, normal by
   `Plancherel.rationalCommonNormKernel_normal`, and `H ⊔ Z(G(k))` has finite
   index by the first result.
3. **Conclusion.** `CentralCharacterProjectivity.projective_and_injective_of_compactRestriction`
   applied to `H`, `χ`, `τ` gives both conjuncts in the full subcategory of the
   property `fun A => A.HasCentralCharacter χ`, which is the target's `C`.

No admissibility, finite-length, unitarity or smoothness hypothesis on `χ` is
used. The five premises are published propositions with open proof tasks; the
final proof of the target applies this theorem to their proofs once those are
published.
