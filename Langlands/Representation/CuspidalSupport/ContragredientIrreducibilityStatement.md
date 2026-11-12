# Irreducibility of the contragredient (Renard VI.2.2, Corollary): statement

Module `Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityStatement`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `u, v`.
The module contains one **statement**, the `Prop`-valued definition
`ContragredientIrreducibilityStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.2.2, printed p.140 / PDF p.146:

> **Corollaire.** Soit `(π, V)` une représentation lisse de `G`. Alors `π` est
> irréductible (resp. supercuspidale irréductible) si et seulement si `π̃` est
> irréductible (resp. supercuspidale irréductible).
>
> *Démonstration.* Ceci découle du théorème et du corollaire III.1.7.

The Theorem of VI.2.2 (irreducible implies admissible) is the published
`RationalPointsIrreducibleAdmissibleStatement`. Before this unit no declaration
stated the Corollary.

## The statement

In the represented-parabolic setting of the published VI.10.4 statements
(nonarchimedean local field `k` with `T2Space`, connected reductive `G`, canonical
topology `RationalPointFamily.pointTopology` on `G(F)`, `LocallyCompactSpace` and
`NonarchimedeanGroup` binders), for every `A : SmoothRep.{0, u, v} ℂ G(F)`:

- `A.IsIrreducible ↔ A.contragredient.IsIrreducible`, and
- `A.IsIrreducible ∧ IsSupercuspidal A ↔
  A.contragredient.IsIrreducible ∧ IsSupercuspidal A.contragredient`.

`A.contragredient` is the published smooth contragredient (smooth linear forms
with the inverse-transpose action); its carrier lies in the same universe `v`.
`IsSupercuspidal` is the published represented predicate
`Aubert.General.RepresentedParabolic.IsSupercuspidal`: every normalized Jacquet
module along a proper actual rational parabolic vanishes (VI.2.1, definition).

## Why the statement is true

If `π` is irreducible it is admissible (VI.2.2, Theorem), so `π̃` is irreducible by
III.1.7. Conversely, if `π̃` is irreducible it is admissible. Since
`(π̃)^K` is the dual of `π^K`, `π` is admissible, so `π ≅ π̃̃` is irreducible.
For supercuspidality: by VI.2.1 an irreducible representation is supercuspidal
iff its coefficients have compact support modulo the centre. The coefficients of
`π̃` are those of `π` composed with `g ↦ g⁻¹`.

## Remaining obligations

The proof is a separate obligation. It needs the published VI.2.2 Theorem, the
III.1.7 Corollary and the VI.2.1 characterization (check the Library for their
proofs).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Category.Contragredient` | `SmoothRep.contragredient` |
| `Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport` | `Aubert.General.RepresentedParabolic.IsSupercuspidal`, the represented point topology |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
