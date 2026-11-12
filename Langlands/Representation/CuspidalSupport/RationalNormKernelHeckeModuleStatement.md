# Right `H(G, ρ)`-module structures and the adjunction: statement

Module `Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeModuleStatement`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF, uV`.
The module contains one **statement**, the `Prop`-valued definition
`RationalNormKernelHeckeModuleStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.4.1–VI.4.2, printed pp.149–153 / PDF pp.155–159. The
statement covers the paragraphs after the Proposition of VI.4.2, printed
pp.152–153 / PDF pp.158–159:

> Soit `(τ, E)` une représentation dans `M(G)[π]`. L'algèbre `R = End_G(Π)`
> agit (à droite) sur `Hom_G(Π, τ)`. On obtient une structure de `A`-module à
> droite sur `Hom_G(Π, τ)` par transport de structure, c'est-à-dire
> `s · φ = s ∘ α_φ`. […] D'autre part, l'algèbre `A` agit à droite sur
> `Hom_{⁰G}(ρ, Res τ)` par
> `(ψ · φ)(w) = ∑_{ḡ ∈ G/⁰G} τ(g) · ψ(φ(g⁻¹) · w)`, […]. L'isomorphisme
> naturel d'adjonction (VI.4.1.1) `Hom_G(Π, τ) ≃ Hom_{⁰G}(ρ, Res τ)` est alors
> un morphisme de `A`-modules à droite. […] Il est réalisé par l'application
> (VI.4.2.5) `α ↦ ψ_α`, `ψ_α(w) = α(f_w)`, […] son inverse est
> (VI.4.2.6) `ψ ↦ α_ψ`, `α_ψ(f) = ∑_{ḡ ∈ ⁰G\G} τ(g) · ψ(f(g⁻¹))`.

Here `A = H(G, ρ)`, `Π = ind_{⁰G}^G(ρ)`, and `α_φ ∈ R` corresponds to
`φ ∈ A` under the isomorphism of the Proposition. The Library's VI.4 map
(`notes/renard/supercuspidal-block-center-progress.md`) records: "The right
module structures of VI.4.2 are not formalized."

The provenance is source.

## Published objects

All objects are published; this file constructs nothing. The binders follow
the published VI.4.2 Proposition `RationalNormKernelHeckeStatement`:

- a nonarchimedean local field `F`, a connected reductive `G`, the canonical
  topology on `G(F)` (a topological group), and an irreducible smooth `ρ`
  (carrier in `Type uV`) of the common norm kernel `⁰G =
  rationalCommonNormKernel G`;
- `I = Π`, the published compact induction
  `(compactInductionFunctor ⁰G).obj ρ` (carrier in `Type (max uF uV)`), and
  `f_w = unitFunction … w`, the function supported on `⁰G` with
  `f_w(h) = ρ(h) w` (so `f_w(1) = w`), as in the published Proposition;
- `rationalNormKernelHecke G ρ` (Renard's `H(G, ρ)`, (VI.4.2.1)) and
  `rationalNormKernelConvolution G ρ` (its convolution, summed over chosen
  representatives `q.out` of `G/⁰G`);
- `τ`, an arbitrary smooth representation of `G(F)` with carriers in
  `Type (max uF uV)` (those of `Π`), its restriction
  `SmoothRep.restrictSubgroup ⁰G τ`, and `⁰G`-maps
  `ψ : ρ → Res τ` as `Representation.IntertwiningMap`s;
- `eval` evaluates an element of `Π` at a point; `LeftQuotient ⁰G` is the
  coset space `⁰G\G`.

## The statement

With `(ψ · φ)(w) = ∑ᶠ_{q ∈ G/⁰G} τ(q.out) ψ(φ(q.out⁻¹) w)` (`act` in the Lean
file):

1. for every `⁰G`-map `ψ` and `φ ∈ H(G, ρ)`, `ψ · φ` is again a `⁰G`-map;
2. `(ψ · φ) · φ' = ψ · (φ ∗ φ')`, and every `φ_e ∈ H(G, ρ)` with
   `φ_e(h) = ρ(h)` on `⁰G` and `φ_e = 0` off `⁰G` (the unit of `H(G, ρ)`)
   acts trivially. So this is a right `H(G, ρ)`-module structure;
3. for every linear equivalence `e : End Π ≃ H(G, ρ)` with
   `e(α)(g)(w) = α(f_w)(g)` (the published Proposition asserts that such an
   `e` exists and is an algebra isomorphism), every `s : Π → τ`, `φ` and the
   `⁰G`-map `ψ = ψ_s`, `ψ_s(w) = s(f_w)`:
   `ψ_{s ∘ e⁻¹(φ)} = ψ_s · φ`. The left side is the adjunction map applied to
   the transported right action `s · φ = s ∘ α_φ`;
4. for every `⁰G`-map `ψ` there is exactly one `s : Π → τ` with `ψ_s = ψ`,
   and it is given by (VI.4.2.6):
   `s(v) = ∑ᶠ_{q ∈ ⁰G\G} τ(q.out) ψ(v(q.out⁻¹))`.

Items 3 and 4 say that the adjunction (VI.4.1.1) is a bijection, realized by
(VI.4.2.5) with inverse (VI.4.2.6), and that it is a morphism of right
`H(G, ρ)`-modules.

## Formal choices

- **`τ` arbitrary.** Renard takes `τ ∈ M(G)[π]`; the assertions hold for
  every smooth `τ`, and the statement quantifies over all of them. Renard's
  remark that the action "dépend de `τ`, et non pas seulement de `Res τ`" is
  visible in the formula and is not a separate assertion.
- **Sums over representatives.** The sums use the chosen representatives
  `q.out`, as in the published convolution and in the published inverse
  formula; the summands do not depend on the representative because `⁰G` is
  normal and `ψ` is `⁰G`-equivariant.
- **Right action on `Hom_G(Π, τ)`.** Defined by transport, `s · φ = s ∘ α_φ`,
  with `α_φ = e⁻¹(φ)` written as `e.symm φ ≫ s` (first `α_φ`, then `s`). The
  statement quantifies over `e` satisfying the defining formula of the
  published Proposition; that formula determines `e`.
- **Universes.** `ρ` has carriers in `Type uV`; `Π` and `τ` in
  `Type (max uF uV)`, the universe of compact induction.

## Why the statement is true

The summands `τ(g) ψ(φ(g⁻¹) w)` depend only on `g⁰G`, and only finitely many
cosets contribute. Equivariance (1) uses `φ(g⁻¹h) = φ(g⁻¹)ρ(h)` and
`hg ∈ g⁰G`. Item 2 is a change of variables `x = gy` in the double sum,
giving `∑_x τ(x) ψ((φ ∗ φ')(x⁻¹) w)`. Item 3 uses the decomposition
(VI.4.2.2) `f = ∑_{ḡ ∈ ⁰G\G} r(g⁻¹) f_{f(g)}`, the `G`-equivariance of `s`,
and `α_φ(f_w)(g) = e(α_φ)(g)(w) = φ(g)(w)`. Item 4 follows from the same
decomposition: `s` is determined by the `s(f_w)`, and the displayed formula
defines a `G`-map with `s(f_w) = ψ(w)`.

## Remaining obligations

The proof is a separate obligation. It needs the published VI.4.2
Proposition's objects, the decomposition (VI.4.2.2) of elements of the
compact induction, and the normality of `⁰G` in `G(F)`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStatement` | `rationalNormKernelHecke`, `rationalNormKernelConvolution`, and through it `compactInductionFunctor`, `unitFunction`, `eval`, `LeftQuotient`, `rationalCommonNormKernel`, `SmoothRep.restrictSubgroup`, `rationalPoint_isTopologicalGroup` |
