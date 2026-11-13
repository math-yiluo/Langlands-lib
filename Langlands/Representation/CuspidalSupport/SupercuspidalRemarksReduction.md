# Renard VI.2.1 remarks, reduced to the joint special compact basis statement

Module `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksReduction`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

The module contains one **statement** and its proof:

- `SupercuspidalRemarksReductionStatement : Prop` is the implication
  `JointSpecialCompactBasisExistenceStatement.{u} → SupercuspidalRemarksStatements.{u, v}`;
- `supercuspidalRemarksReduction : SupercuspidalRemarksReductionStatement.{u, v}`
  proves it.

This is a **conditional** result. It does not prove `SupercuspidalRemarksStatements`
outright. That still needs a proof of
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
(Task 4169). Once such a proof is in the Library, applying
`supercuspidalRemarksReduction` to it proves the target statement.

## Provenance

This is a derived statement. The consequent is the published
`SupercuspidalRemarksStatements`, which formalizes the remarks of David Renard,
*Représentations des groupes réductifs p-adiques* (French edition dated 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), VI.2.1,
printed pp.137–139 / PDF pp.143–145. See that statement's Markdown for the quoted
source text.

The premise is the published `JointSpecialCompactBasisExistenceStatement`. It is
not a hypothesis of Renard's remarks. It is the premise under which the Library
currently proves Renard's VI.2.1 implication "supercuspidal ⇒ compact on `⁰G`"
(`compactRestriction_of_isSupercuspidal`), which the forward halves of the second
and third remarks need. The Library has no other route to that implication. The
reduction records exactly that dependency: every other step uses theorems already
proved in the Library or in the companion module `SupercuspidalRemarksGeneric`.

## Setting

As in the target: a nonarchimedean local field `k` with `T2Space`, a connected
reductive `G`, the canonical topology `RationalPointFamily.pointTopology` on
`G(F) = rationalPoints G`, and the `LocallyCompactSpace` and `NonarchimedeanGroup`
binders. Write `Z = Subgroup.center G(F)` and `H = ⁰G`, the common kernel of the
norms of the rational characters
(`Plancherel.rationalCommonNormOpenSubgroup G`, an open subgroup). "Compact on `H`"
means `HasCompactSmoothDualCoefficients (A.representation.comp H.subtype)`. This is
definitionally the Library's `HasCompactNormKernelRestriction A`, which is stated
through `SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A`.

## Proof

After introducing the setting, the proof gathers these facts:

- `H` is normal (`Plancherel.rationalCommonNormKernel_normal`).
- `H Z` has finite index in `G(F)`
  (`CuspidalSupport.rationalCommonNormKernel_sup_center_finiteIndex`).
- `H ∩ Z` is compact (`Plancherel.isCompact_rationalCommonNormKernel_inf_center`).
- Some compact open subgroup `K₀` exists
  (`Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup`).
- Compact on `H` ⇒ supercuspidal: `isSupercuspidal_of_compactRestriction` (VI.2.1,
  (c) ⇒ (a)). Its premises are discharged by the published proofs
  `GroupScheme.parabolicDynamic`, `GroupScheme.smoothMaximalSplitTorusConjugacy`,
  `GroupScheme.standardCocharacter` and `GroupScheme.relativeRootSystem`.
- Supercuspidal ⇒ compact on `H`: `compactRestriction_of_isSupercuspidal` (VI.2.1,
  (a) ⇒ (c)), with `parabolicDynamic`, `standardCocharacter`,
  `relativeRootSystem` and the premise `hJoint`. This is the only use of `hJoint`.

Then the three conjuncts:

1. **Subquotients.** Directly `IsSupercuspidal.of_isSubquotient`.
2. **Compact centre.** Assume `Z` is compact.
   - (⇒) A supercuspidal `A` is compact on `H`. By
     `support_subset_mul_center_of_comp` (uses `H` open normal, `H Z` of finite
     index, `A` smooth), for each compact open `K` and each `w` there is a compact
     `C` with the support of `g ↦ ℓ(A(g⁻¹) w)` in `C Z` for all `K`-invariant `ℓ`.
     Since `Z` is compact, `hasCompactSmoothDualCoefficients_of_support_of_isCompact_center`
     (with `K₀`) gives compact coefficients on `G(F)`.
   - (⇐) Compact coefficients on `G(F)` restrict to the open subgroup `H`
     (`hasCompactSmoothDualCoefficients_comp_openSubgroup`). Then `A` is
     supercuspidal by the (c) ⇒ (a) step.
3. **The `f_{K,w}` criterion.**
   - (⇒) A supercuspidal `A` is compact on `H`. Then
     `support_subset_mul_center_of_comp` gives exactly the support condition.
   - (⇐) The support condition, `H ∩ Z` compact and `K₀` give compact coefficients
     on `H` (`hasCompactSmoothDualCoefficients_comp_of_support`). Then `A` is
     supercuspidal by the (c) ⇒ (a) step.

The generic lemmas named here are explained in `SupercuspidalRemarksGeneric.md`. The
argument in the third remark follows Renard's hint for the second Remark 2 (adapt
IV.1.3, using that `⁰G Z` has finite index and `⁰G ∩ Z` is compact).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksStatements` | the target `SupercuspidalRemarksStatements` |
| `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksGeneric` | the generic lemmas (companion module) |
| `Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex` | `rationalCommonNormKernel_sup_center_finiteIndex` |
| `Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal` | `isSupercuspidal_of_compactRestriction`, `compactRestriction_of_isSupercuspidal`, `JointSpecialCompactBasisExistenceStatement` (transitively) |
| `Langlands.Representation.Exponents.RepresentedCuspidalProjection` | `IsSupercuspidal.of_isSubquotient` |
| `Langlands.Representation.Plancherel.RationalNormKernelTopology` | `rationalCommonNormOpenSubgroup` |
| `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` | `parabolicDynamic` |
| `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof` | `smoothMaximalSplitTorusConjugacy` |
| `Langlands.GroupScheme.Rational.StandardCocharacterProof` | `standardCocharacter` |
| `Langlands.GroupScheme.Rational.RelativeRootSystemProof` | `relativeRootSystem` |
