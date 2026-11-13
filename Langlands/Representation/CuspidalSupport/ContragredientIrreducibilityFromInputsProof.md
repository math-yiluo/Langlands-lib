# Proof of `ContragredientIrreducibilityFromInputsStatement`

Author: Worker 154. Lean module
`Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityFromInputsProof`,
namespace `Langlands.CuspidalSupport`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: VI.2.2,
Corollary (printed p.140 / PDF p.146), proved there by "Ceci découle du théorème et du
corollaire III.1.7". The supercuspidal half here goes through VI.9.6, second Theorem
(printed p.201 / PDF p.207), instead of the coefficient characterization of VI.2.1; see
"Route" below.

## Main declaration

### `contragredientIrreducibilityFromInputs`

```text
theorem contragredientIrreducibilityFromInputs :
    ContragredientIrreducibilityFromInputsStatement.{u, v}
```

Its type is exactly the published statement
[`ContragredientIrreducibilityFromInputsStatement`](ContragredientIrreducibilityFromInputsStatement.md):
from `hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v}` (Jacquet's theorem) and
`hCas : LeviJacquetContragredientStatement.{u, v}` (VI.9.6, second Theorem) it proves
`ContragredientIrreducibilityStatement.{u, v}`. It has no further hypothesis.
Inspection reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Proof. Fix `k`, `G`, `hG`, the point topology `RationalPointFamily.pointTopology`, the
`LocallyCompactSpace` and `NonarchimedeanGroup` instances, and `A`.

1. **Cofinality.** `Aubert.General.compactOpenCofinal_of_nonarchimedean` (imported from `AlternatingOperator`) gives
   `CompactOpenCofinal (rationalPoints G)`.
2. **Irreducibility, `A ⇒ Ã`.** If `A` is irreducible, `hAdm k G hG A` makes it
   admissible. (`rationalPoints G` is definitionally `RationalPoint k G.X`, and
   `RationalPointFamily.pointTopology` is defined as `rationalPointTopology k G.X`, so
   `hAdm` applies to `A` as it stands.) The published
   `SmoothRep.isIrreducible_contragredient_iff` (an admissible representation is
   irreducible exactly when its smooth contragredient is; Renard III.1.7) then gives
   `Ã` irreducible.
3. **Irreducibility, `Ã ⇒ A`.** The published `isIrreducible_of_smoothContragredient`
   says that if smooth linear forms separate points on every smooth representation, then
   a smooth representation whose contragredient is irreducible is irreducible. Smooth
   separation is the published `smoothBidual_injective_of_compact_cofinal`, from step 1.
   No admissibility is used here.
4. **Supercuspidality, `A ⇒ Ã`.** `isSupercuspidal_contragredient_of_leviJacquetContragredient`
   (below), applied to `hCas`.
5. **Supercuspidality, `Ã ⇒ A`.** If `Ã` is irreducible and supercuspidal, then `A` is
   irreducible by step 3 and admissible by `hAdm`. Step 4 applied to `Ã` makes the bidual
   `Ã~` supercuspidal. The published `SmoothRep.bidualIso` gives `A ≅ Ã~` for admissible
   `A` (with step 1), and `isSupercuspidal_of_iso` (below) transfers supercuspidality
   back to `A`.

## Helper declarations

- The imported `Aubert.General.compactOpenCofinal_of_nonarchimedean`: in a locally compact nonarchimedean topological
  group, every open subgroup contains a compact open subgroup. Take a compact
  neighbourhood `C` of `1` (`exists_compact_mem_nhds`). `C ∩ K` is a neighbourhood of
  `1`, so it contains an open subgroup `V` (nonarchimedean). `V` is closed, being an open
  subgroup, and lies in the compact `C`, so it is compact; it lies in `K`.
- `subsingleton_contragredient`: if the carrier of a smooth representation `X` is a
  subsingleton, so is the carrier of `X.contragredient`. Two smooth linear forms agree on
  the only vector `0`.
- `not_isIso_oppositeLeviParabolic_inclusion`: if `p : P ⟶ G` is not an isomorphism,
  neither is the inclusion of the actual opposite parabolic
  `oppositeLeviParabolic hG p l hp hl`. If it were, the published
  `IsRationalLeviSubgroup.isIso_of_isIso_parabolic` would make its Levi inclusion an
  isomorphism. Then `l ≫ p` (equal to the opposite's `levi ≫ inclusion` by its field
  `levi_comp`) is an isomorphism, so its range is all of `G` (`full_range_of_isIso`).
  Since the range of `l ≫ p` lies in the range of `p`
  (`SubgroupFunctor.range_comp_le`), the range of `p` is all of `G`. As `p` is a closed
  subgroup, hence a monomorphism (`IsClosedSubgroup.mono_overHom`), the published
  `isIso_of_full_range` makes `p` an isomorphism, a contradiction. The order on
  `SubgroupFunctor G` has no `OrderTop` instance, so `range p ≤ ⊤` is checked carrier by
  carrier (`SubgroupFunctor.le_def`, `SubgroupFunctor.top_carrier`).
- `isSupercuspidal_of_iso`: if `A ≅ B` and `B` is supercuspidal, so is `A`. For each
  proper parabolic, the Jacquet functor maps the isomorphism to an isomorphism of Jacquet
  modules, hence a linear equivalence of carriers (`SmoothRep.equivOfIso`), which
  transfers the subsingleton property.
- `isSupercuspidal_contragredient_of_leviJacquetContragredient`: from `hCas`, if `A` is
  supercuspidal then so is `Ã`. Let `P = MU` be a proper actual rational parabolic
  (`p`, `l`, `r`), and let `P̄ = MŪ` be the published unconditional actual opposite
  `oppositeLeviParabolic hG p l hp hl` (module
  `Langlands.Representation.LanglandsClassification.OppositeLeviParabolic`). Its fields
  give a parabolic, rational Levi and geometric unipotent radical with the multiplication
  isomorphism, the same Levi homomorphism (`levi ≫ inclusion = l ≫ p`) and
  `pointImage p ⊓ pointImage inclusion = pointImage (l ≫ p)`. Apply `hCas` with the
  opposite in the role of the statement's `P` and the given `P` in the role of `P̄`: the
  two compatibility hypotheses are `levi_comp.symm` and `intersection` after `inf_comm`.
  This gives a natural isomorphism `e` whose component at `A` is
  `r_P^G(Ã) ≅ (r_{P̄}^G A)~` (with `leviJacquetFunctor`). `P̄` is proper by
  `not_isIso_oppositeLeviParabolic_inclusion`, so `A` supercuspidal makes the Jacquet
  module `(jacquetFunctor …).obj A` along `P̄` a subsingleton. `leviJacquetFunctor` is
  `jacquetFunctor` followed by pullback along `leviPointsEquiv`, with the same carrier, so
  `subsingleton_contragredient` makes `(r_{P̄}^G A)~` a subsingleton, and
  `e.app (op A)` transfers this to `r_P^G(Ã)`. The Levi topology needed to form
  `leviJacquetFunctor` on `M(F)` is `leviPointTopology` of the opposite's Levi, with
  `leviPoints_nonarchimedeanGroup` for its topological group structure; it is the same
  topology as the one built from `l`, since `leviPointTopology` is
  `RationalPointFamily.pointTopology` on `M`.

## Route

Renard proves the supercuspidal half from the Theorem and III.1.7 together with the
VI.2.1 characterization by coefficients compactly supported modulo the centre. The
Library's published VI.2.1 statements use the standard-parabolic cuspidality predicate
and further structural premises, not the represented predicate `IsSupercuspidal` of the
target. This proof uses Casselman's pairing in the form of VI.9.6 (second Theorem)
instead, together with the unconditional opposite parabolic `oppositeLeviParabolic`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityFromInputsStatement` | the statement and its premises; transitively the smooth contragredient API (`SmoothRep.contragredient`, `SmoothRep.bidualIso`, `SmoothRep.isIrreducible_contragredient_iff`), `isIrreducible_of_smoothContragredient`, `smoothBidual_injective_of_compact_cofinal`, `IsSupercuspidal`, `jacquetFunctor`, `leviJacquetFunctor`, `leviPointTopology`, `leviPoints_nonarchimedeanGroup`, `SmoothRep.equivOfIso` |
| `Langlands.Representation.LanglandsClassification.OppositeLeviParabolic` | `oppositeLeviParabolic` |
| `Langlands.GroupScheme.Rational.FullParabolicLevi` | `IsRationalLeviSubgroup.isIso_of_isIso_parabolic` |
| `Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction` | `isIso_of_full_range`, `full_range_of_isIso` |
| `Langlands.GroupScheme.Dynamic.ParabolicLieCriterion` | `SubgroupFunctor.range_comp_le` |
| `Langlands.GroupScheme.ClosedSubgroupMonomorphism` | `IsClosedSubgroup.mono_overHom` |
