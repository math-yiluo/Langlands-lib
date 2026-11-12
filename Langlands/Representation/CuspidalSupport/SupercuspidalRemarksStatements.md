# Remarks on supercuspidal representations (Renard VI.2.1): statement

Module `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksStatements`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.
The module contains one **statement**, the `Prop`-valued definition
`SupercuspidalRemarksStatements`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.2.1, printed pp.137–139 / PDF pp.143–145. After the
definition (printed p.137):

> *Remarques.* 1. Une représentation lisse `(π, V)` de `G` est supercuspidale si
> pour tout sous-groupe parabolique propre standard `P = MN` de `G`, `r_P^G(V)` est
> nul. — 2. Comme `r_P^G` est exact, tout sous-quotient d'une représentation
> supercuspidale est supercuspidal.

After the proof of the Theorem (printed p.139):

> *Remarques.* 1. Si le centre de `G` est compact, une représentation est compacte si
> et seulement si elle est supercuspidale. — 2. Une autre condition équivalente pour
> qu'une représentation `(π, V)` soit supercuspidale est que les fonctions `f_{K,v}`
> définies en IV.1.3 soient à support compact modulo `Z(G)`.

The general subquotient theorem already exists as
`Langlands.Aubert.General.RepresentedParabolic.IsSupercuspidal.of_isSubquotient`
in `RepresentedCuspidalProjection.lean`. This unit packages that assertion with
the two other general remarks as a single statement. The first remark of the first block, that standard parabolics
suffice, compares the represented predicate with the standard-family one. It needs
the conjugacy of parabolics to standard ones, and it is not stated here (see
"Not stated").

## The statement

The setting is the represented one of the published VI.10.4 statements:
nonarchimedean local field `k` with `T2Space`, connected reductive `G`, canonical
topology `RationalPointFamily.pointTopology`, and the `LocallyCompactSpace` and
`NonarchimedeanGroup` binders. Write `Z = Subgroup.center G(F)`, and let
`IsSupercuspidal` be the published represented predicate (every normalized Jacquet
module along a proper actual rational parabolic vanishes). The conjunction asserts:

1. for all smooth `A`, `B` with `B` a subquotient of `A`
   (`SmoothRep.IsSubquotient`), `IsSupercuspidal A → IsSupercuspidal B`;
2. if `Z` is compact, then for every smooth `A`, `IsSupercuspidal A` holds iff
   `HasCompactSmoothDualCoefficients A.representation` (the published IV.1
   compactness: every coefficient against a smooth vector of the dual has compact
   support);
3. for every smooth `A`, `IsSupercuspidal A` holds iff for every compact open `K`
   and every `w ∈ A` there is a compact `C` such that, for every `K`-invariant
   linear form `ℓ`, the support of `g ↦ ℓ(A(g⁻¹) w)` lies in `C · Z`.

## Formalization choices

- **`f_{K,w}`.** IV.1.3 defines `f_{K,w}(g) = A(e_K) A(g⁻¹) w`. A `K`-invariant
  linear form satisfies `ℓ ∘ A(e_K) = ℓ`, and every linear form on `A^K` extends
  through the projector `A(e_K)`. So `f_{K,w}(g) ≠ 0` iff some `K`-invariant `ℓ`
  has `ℓ(A(g⁻¹) w) ≠ 0`. The support of `f_{K,w}` is the union in item 3. The
  same device is used in the published VI.2.4 statement and in
  `HasUniformFixedLevelCoefficientSupport`.
- **Compact modulo the centre** is containment in `C · Z` for a compact `C`. That
  set is closed, so the condition does not depend on taking the closure of the
  support. `Z` is the centre of the abstract group `G(F)`, as in the published
  `RepresentedSupercuspidalCentralProjectivityStatement`.
- **Compact centre.** Renard's "le centre de `G` est compact" is
  `IsCompact Z`.

## Not stated

Remark 1 of the first block, the equivalence of the represented predicate with
vanishing along proper *standard* parabolics only, is not stated. It is a
comparison between the represented interface and the standard-family interface
(`Aubert.General.IsCuspidal` for `parabolic i ν`). It needs every proper rational
parabolic to be `G(F)`-conjugate to a standard one (Chapter V), together with the
transport of Jacquet modules under conjugation.

## Why the statement is true

1. `r_P^G` is exact (published VI.1.2 statements), so the Jacquet modules of a
   subquotient are subquotients of zero modules.
2. If `Z` is compact, the maximal split central torus is trivial, so `G` has no
   nontrivial rational characters and `⁰G = G`. The published VI.2.1 Theorem,
   (a) ⇔ (c), then says supercuspidal ⇔ compact.
3. Renard: adapt the proof of Theorem IV.1.3, using that `⁰G Z` has finite index
   in `G(F)` and that `⁰G ∩ Z` is compact (V.2.6).

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Category.Subquotients` | `SmoothRep.IsSubquotient` |
| `Langlands.Representation.CompactCoefficient.Classes` | `HasCompactSmoothDualCoefficients` |
| `Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport` | `IsSupercuspidal`, the represented point topology |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
