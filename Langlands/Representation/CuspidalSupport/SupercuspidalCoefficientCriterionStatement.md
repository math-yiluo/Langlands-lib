# Supercuspidality by coefficients (Renard VI.2.1, Theorem (a) ⇔ (b)): statement

Module `Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionStatement`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.
The module contains one **statement**, the `Prop`-valued definition
`SupercuspidalCoefficientCriterionStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.2.1, printed pp.137–139 / PDF pp.143–145:

> **Théorème.** Soit `(π, V)` une représentation lisse de `G`. Les conditions
> suivantes sont équivalentes : a) `(π, V)` est supercuspidale, b) Les
> coefficients matriciels de `(π, V)` sont à support compact modulo le centre
> `Z(G)`, c) la restriction de `(π, V)` à `⁰G` est compacte.

The Library states (a) ⇒ (c) and (c) ⇒ (a) (`RationalCuspidalCompactRestrictionStatement`
and `RationalCompactRestrictionCuspidalStatement`, both proved). Condition (b)
appears only in `SupercuspidalUnitaryCoefficientCompactSupportStatement`, for
irreducible representations with unitary central character and smooth-dual
coefficient norms. This unit states (a) ⇔ (b) for every smooth representation.

## The statement

The setting is the represented one of the published VI.10.4 statements:
nonarchimedean local field `k` with `T2Space`, connected reductive `G`, canonical
topology `RationalPointFamily.pointTopology`, and the `LocallyCompactSpace` and
`NonarchimedeanGroup` binders. For every `A : SmoothRep.{0, u, v} ℂ G(F)`, the
statement asserts `IsSupercuspidal A` iff for every `w ∈ A` and every linear form
`ℓ` that is a smooth vector of the dual action, there is a compact `C ⊆ G(F)` with
`Function.support (matrixCoefficient A.representation ℓ w) ⊆ C · Z`. Here the
matrix coefficient is `g ↦ ℓ(A(g) w)` and `Z = Subgroup.center G(F)`.

## Formalization choices

- **Coefficients** are the published `matrixCoefficient` against smooth vectors
  of the algebraic dual action, as in the published IV.1 predicate
  `HasCompactSmoothDualCoefficients`. Renard's coefficients use the smooth dual
  `Ṽ`, and those are exactly these forms.
- **Compact support modulo the centre** is containment of the support in `C · Z`
  for a compact `C`. That set is closed, so the closure of the support makes no
  difference. `Z` is the centre of the abstract group `G(F)`, as in the published
  `RepresentedSupercuspidalCentralProjectivityStatement`.
- **Supercuspidality** is the published represented predicate (vanishing of the
  normalized Jacquet modules along proper actual rational parabolics).

## Why the statement is true

Following Renard: (b) ⇒ (c) restricts coefficients to `⁰G`. Since `⁰G ∩ Z` is
compact and `⁰G Z` has finite index (V.2.6), a set compact modulo `Z` meets `⁰G` in
a relatively compact set. (c) ⇒ (a) is the proved Library implication. (a) ⇒ (b)
follows from (c) and the finiteness of `G/⁰G Z`.

## Remaining obligations

The proof is a separate obligation. It needs the framework comparison between the
represented predicate and the standard-family cuspidality used by the proved
(a) ⇔ (c) statements.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CompactCoefficient.Classes` | `matrixCoefficient`, `IsSmoothVector` (through its imports) |
| `Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport` | `IsSupercuspidal`, the represented point topology |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
