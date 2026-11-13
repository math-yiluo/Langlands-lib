# Induction from an open subgroup: the Hecke inclusion (Renard III.2.6, final Remark): statement

Module `Langlands.Representation.Hecke.OpenSubgroupInclusionStatement`. Namespace
`Langlands.Hecke.Homomorphism`. Universe parameters `uG` (the group) and `v` (module
carriers).
The module contains one **statement**, the `Prop`-valued definition
`OpenSubgroupHeckeInclusionStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published map
[iii2-hecke-induction](../../../notes/renard/iii2-hecke-induction.md) (Task 5296) lists the
final Remark of III.2.6 as a retained gap: "This exact extension/inclusion bimodule comparison
and the resulting Hecke pseudo-forgetful comparison for all open subgroups are not separately
packaged here. A direct general-open-subgroup triviality theorem for
`HH.relativeModularCharacter` is also not supplied". The Remark's adjunction (III.2.6.5) is
already proved as `Langlands.Induction.compactInductionAdjunction`
([OpenAdjunction](../Induction/OpenAdjunction.md)) and is not restated.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.2.6, printed p.77 / PDF p.83:

> Remarque. Nous terminons cette section en étudiant le cas de l'induction à partir d'un
> sous-groupe ouvert `H` de `G` (la topologie étant totalement discontinue, `H` est aussi
> fermé dans `G`). Dans ce cas, on a une inclusion évidente `H(H) ↪ H(G)`, où l'on identifie
> `H(H)` à l'espace des distributions dans `H(G)` à support dans `H`. La structure de
> `H(H)`-bimodule non dégénéré de `H(G)` décrite précédemment et utilisant les
> représentations `l` et `r` de `H` sur `H(G)` peut se décrire ici plus simplement comme la
> structure de bimodule donnée par l'inclusion d'algèbres de `H(H)` dans `H(G)`. Dans ce
> cadre, nous avons remarqué à la fin de la section I.2.3 que le foncteur d'oubli et le
> pseudo foncteur d'oubli sont isomorphes. Ce qui nous intéresse ici est le fait que par
> conséquent le foncteur d'oubli `Res_H^G` admet un adjoint à gauche, en plus de l'adjoint à
> droite `Ind_H^G`, et que celui-ci est donné par `ind_H^G` (le facteur `δ_{H\G}` est trivial
> dans ce cas, puisque `μ_H` est, au choix d'un facteur multiplicatif près, la restriction de
> `μ_G` à `H`). On a donc […] un isomorphisme naturel (III.2.6.5) […].

## Published objects used

- `HeckeAlgebra μ`, the Hecke algebra of a Haar measure `μ`: the test functions `SchwartzBruhat`
  with convolution for `μ` ([Convolution](Convolution.md)).
- `leftModule μG μH φ hφ` and `rightModule μG μH φ hφ`: the canonical left `H(H)`-action and
  right `H(H)`-action (a left `H(H)ᵐᵒᵖ`-action) on `H(G)` of III.2.1, built from the
  representations `l` and `r` of `H` on `H(G)`; `(a · T)(x) = ∫_H a(h) T(h⁻¹ x) dμH(h)`
  ([HomomorphismLeft](HomomorphismLeft.md), [HomomorphismRight](HomomorphismRight.md)).
- `F μG μH φ hφ` and `pseudoF μG μH φ hφ`: the Hecke forgetful functor `N ↦ H(G) ⊗_{H(G)} N`
  and pseudo-forgetful functor `N ↦ Hom_{H(G)}(H(G), N)_{H(H)}`, both
  `NondegenerateModuleCat (HeckeAlgebra μG) ⥤ NondegenerateModuleCat (HeckeAlgebra μH)`.
- `relativeModularCharacter φ hφ`, the smooth character `δ_G(φ(h)) / δ_H(h)` used for compact
  induction in III.2.6 ([CompactInductionModels](CompactInductionModels.md)).
- `HarmonicAnalysis.HomogeneousFunctions.relativeModular H hH`, Renard's
  `δ_{H\G} = δ_G|_H / δ_H` of II.3.9 for a closed subgroup
  ([HomogeneousFunctions](../../HarmonicAnalysis/HomogeneousFunctions.md)).

Here `φ = H.subtype`, the inclusion of the subgroup.

## The statement

**`OpenSubgroupHeckeInclusionStatement`.** Let `G` be a t.d. group (Hausdorff, locally
compact, nonarchimedean) with a Haar measure `μG`, let `H` be an open subgroup and `μH` a Haar
measure on `H`. Then:

1. `δ_{H\G}` is trivial: `relativeModularCharacter H.subtype _` takes the value `1`, and so
   does `relativeModular H _`;
2. the pseudo-forgetful functor `pseudoF` is naturally isomorphic to the forgetful functor `F`;
3. if `μH(s) = μG(s)` for every `s ⊂ H` (`μH` is the restriction of `μG`), there is a
   nonunital ring homomorphism `ext : H(H) → H(G)` such that
   - `ext(a)(h) = a(h)` for `h ∈ H` and `ext(a)(x) = 0` for `x ∉ H` (extension by zero);
   - every `T ∈ H(G)` vanishing outside `H` is some `ext(a)`;
   - the canonical actions are multiplication through `ext`: `a · T = ext(a) * T` and
     `T · a = T * ext(a)`.

## Formalization choices

- **The identification `H(H) ↪ H(G)`.** Renard identifies `H(H)` with the distributions on
  `G` supported in `H`, which needs no choice of measure. In the published Hecke algebras a
  distribution is a test function times the Haar measure. When `μH` is the restriction of
  `μG`, the identification is extension by zero of densities, and the statement asserts
  exactly that. For another Haar measure `μH = c⁻¹ μG|_H` the identification is
  `a ↦ c⁻¹ ext(a)`. That case is not stated separately.
- **Restriction of measures.** The hypothesis is stated for all subsets, as an equality of
  outer measures. `μG.comap Subtype.val` satisfies it, since the inclusion of an open subset
  is a measurable embedding (`MeasurableEmbedding.comap_apply`).
- **Triviality of `δ_{H\G}`.** The Library has two published forms of the relative modular
  character, the smooth character used by the III.2.6 compact-induction functor and the
  II.3.9 character used for the quotient functional. The statement asserts that both are
  trivial.
- **Clauses 1 and 2 hold for every Haar measure `μH`.** Only the explicit inclusion in clause 3
  uses the restriction hypothesis.
- **(III.2.6.5)**, the adjunction `ind_H^G ⊣ Res_H^G`, is the published proved
  `compactInductionAdjunction` and is not restated.

## Why the statement is true

1. The restriction of `μG` to the open subgroup `H` is a left Haar measure on `H`. Right
   translation by `h ∈ H` scales it by the modular factor of `G` at `h`. So the modular
   functions of `H` and `G` agree on `H`, and both quotients are `1`.
2. Write `e_K` for the normalized indicator of a compact open subgroup `K ⊂ H`. It lies in
   both Hecke algebras, through extension by zero. For a nondegenerate `H(G)`-module `N`, an
   element `φ ∈ Hom_{H(G)}(H(G), N)` fixed by some `e_K` satisfies
   `φ(b) = φ(b e_K) = b · φ(e_K)`. So `φ ↦ φ(e_K)` identifies the nondegenerate part with
   `N`. The tensor product `H(G) ⊗_{H(G)} N` is also `N`. Both identifications are
   `H(H)`-linear and natural in `N` (I.2.3, end).
3. For `a ∈ H(H)` let `ext(a)` be the extension by zero. It is locally constant with compact
   support, because `H` is open and closed. For the restricted measure,
   `(ext(a) * T)(x) = ∫_G ext(a)(y) T(y⁻¹ x) dμG(y) = ∫_H a(y) T(y⁻¹ x) dμH(y)`. This is the
   formula for `a · T`, and the case `T = ext(b)` gives multiplicativity. For the right
   action, the published `rightModule` is `T · a = ι_G(ι_H(a) · ι_G(T))`, where `ι` is the
   weighted inversion `f ↦ (x ↦ Δ(x) f(x⁻¹))`. This inversion reverses convolution, and it
   commutes with `ext` because `Δ_G = Δ_H` on `H`. So `T · a = T * ext(a)`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.CompactInductionModels` | `relativeModularCharacter`; through its imports `HeckeAlgebra`, `leftModule`, `rightModule`, `F`, `pseudoF` |
| `Langlands.HarmonicAnalysis.HomogeneousFunctions` | `relativeModular` |
