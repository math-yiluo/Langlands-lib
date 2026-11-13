# Smooth induction of the contragredient as a dual (Renard III.2.7, Theorem): statement

Module `Langlands.Representation.Induction.ClosedSubgroupDualityStatement`. Namespace
`Langlands.Induction`. Universe parameters `uG` (the group) and `uV` (the representation
space).
The module contains one **statement**, the `Prop`-valued definition
`ClosedInductionSmoothDualityStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published map
[iii2-hecke-induction](../../../notes/renard/iii2-hecke-induction.md) (Task 5296) records that
the III.2.7 Theorem for an arbitrary closed subgroup, with its quotient-measure pairing, is a
gap. The published restricted result `exists_integralDualEquiv_of_section`
([CompactQuotientSmoothDuality](CompactQuotientSmoothDuality.md)) needs a compact quotient, a
continuous homomorphic section and positivity conditions. The predicates
`IsIntegralDuality` and `IsNaturalIntegralDuality` of
[NaturalIntegralDuality](../Aubert/General/NaturalIntegralDuality.md) are interfaces for
normalized parabolic induction with an integral over a compact subgroup, and the module does
not prove that they hold.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.2.7, printed p.78 / PDF p.84:

> Théorème. Soit `H` un sous-groupe fermé du groupe t.d. `G`, et soit `(ρ, W)` une
> représentation lisse de `H`. On a alors un isomorphisme naturel
> `Ind_H^G(W̃) ≃ ind_H^G(W ⊗ δ_{H\G})^∼`.
> La dualité entre `Ind_H^G(W̃)` et `ind_H^G(W ⊗ δ_{H\G})` est donnée explicitement par la
> formule
> `⟨f, h⟩ = ∫_{H\G} h(g)(f(g)) dν_{H\G}`, `(f ∈ ind_H^G(W ⊗ δ_{H\G}))`, `(h ∈ Ind_H^G(W̃))`.
>
> Démonstration. Il reste à démontrer la formule de dualité. On vérifie facilement que
> l'intégrale est bien définie, et elle donne un morphisme `G`-équivariant de
> `Ind_H^G(W̃)` dans `ind_H^G(W ⊗ δ_{H\G})˜`. On vérifie que ce morphisme est bien un
> isomorphisme grâce aux lemmes III.2.2 et I.4.1.

Here `δ_{H\G} = δ_G|_H / δ_H` and `∫_{H\G} … dν_{H\G}` is the positive right-invariant
linear form, unique up to a positive scalar, on the locally constant functions `φ` on `G`
with `φ(hg) = δ_{H\G}(h) φ(g)` and compact support modulo `H` (II.3.9, printed pp.48–50 /
PDF pp.54–56).

## Published objects used

- `HarmonicAnalysis.HomogeneousFunctions.relativeModular H hH : H →* ℝ≥0`, Renard's
  `δ_{H\G} = δ_G|_H / δ_H`, built from `Distribution.renardModular`, Renard's `δ`
  ([HomogeneousFunctions](../../HarmonicAnalysis/HomogeneousFunctions.md)).
- `renardSpace H hH`, the II.3.9 space of locally constant `δ_{H\G}`-covariant functions with
  compact support modulo `H`, and `rightAction H χ`, right translation on it.
- `smoothInduced H σ` on `SmoothFunctions H σ`, `compactInduced H σ` on
  `CompactFunctions H σ`, and `eval H σ f g = f(g)` ([Definitions](Definitions.md)).
- `twist χ ρ`, the representation `h ↦ χ(h) ρ(h)` for a unit-valued character `χ`
  ([Twist/Definitions](../Twist/Definitions.md)).
- `SmoothDual ρ`, `smoothContragredient ρ` and `smoothDualPairing ρ`: the smooth
  contragredient `(ρ̃, W̃)` and its pairing with `W`
  ([Contragredient/Definitions](../Smooth/Contragredient/Definitions.md)).
- `IsSmooth`, `Representation.Equiv`.

## The statement

**`ClosedInductionSmoothDualityStatement`.** Let `G` be a t.d. group (Hausdorff, locally
compact, totally disconnected), `H` a closed subgroup and `χ : H →* ℂˣ` the character with
`χ(h) = δ_{H\G}(h)`. Let `ν` be a nonzero linear form on `renardSpace H hH` invariant under
right translation. Then for every smooth representation `(ρ, W)` of `H` there is an
equivalence of representations of `G`

```text
Φ : Ind_H^G(W̃) ≃ ind_H^G(W ⊗ δ_{H\G})~
```

such that for every `h ∈ Ind_H^G(W̃)` and `f ∈ ind_H^G(W ⊗ δ_{H\G})` there is `φ` in
`renardSpace H hH` with `φ(g) = h(g)(f(g))` for all `g`, and `⟨Φ h, f⟩ = ν(φ)`.

## Formalization choices

- **The integral over `H \ G`.** Renard's `dν_{H\G}` is the invariant positive functional of
  II.3.9. The statement quantifies over every nonzero right-invariant linear form `ν` on the
  published `renardSpace`. The published `InvariantFunctionalStatement` (Task 5524) asserts
  that such forms exist, form a line, and that the line contains a positive one. So the
  source's functional is one admissible `ν`, and the statement covers it. For any other
  `ν = c ν_{H\G}` with `c ≠ 0` the pairing is scaled by `c`, which is still perfect.
- **The integrand.** The statement asserts that `g ↦ h(g)(f(g))` lies in `renardSpace`.
  This is Renard's "l'intégrale est bien définie". `ν` is then applied to that element.
- **`W ⊗ δ_{H\G}`.** The twist uses a complex unit-valued character `χ`. The hypothesis
  `χ(h) = δ_{H\G}(h)` fixes it uniquely, and it exists because `δ_{H\G}` is positive. Using
  the same published `relativeModular` for the twist and for `renardSpace` keeps the two
  covariances equal. The integrand's covariance comes from the twist, and the invariant
  functional lives on the space of that covariance.
- **Naturality.** Renard asserts a natural isomorphism. The statement asserts, for each `W`,
  an equivalence with the explicit pairing formula. The formula determines `Φ`, since a
  smooth functional on `ind_H^G(W ⊗ δ_{H\G})` is determined by its values. Naturality in
  `W` follows from the formula: for `T : W → W′`, both sides of the naturality square pair
  with `f` to `ν(g ↦ h(g)(T f(g)))`.
- **Smoothness.** `ρ` is smooth, as in the source. `G` carries no measure. `ν` replaces the
  quotient measure.

## Why the statement is true

The integrand `φ(g) = h(g)(f(g))` is locally constant, because `h` and `f` are right
invariant under open subgroups. It has support in `supp f`, which is compact modulo `H`. It
satisfies `φ(xg) = (ρ̃(x) h(g))(χ(x) ρ(x) f(g)) = δ_{H\G}(x) φ(g)`. So `φ ∈ renardSpace`.
The map `h ↦ (f ↦ ν(φ))` is `G`-equivariant by the invariance of `ν`. It lands in smooth
functionals, since a `K`-fixed `h` gives a `K`-fixed functional.

To see that it is bijective, fix a compact open `K` and a system of representatives `Ω` of
`H \ G / K`. By the III.2.2 Lemma, `Ind_H^G(W̃)^K ≅ ∏_ω W̃^{K_ω}` and
`ind_H^G(W ⊗ δ)^K ≅ ⊕_ω W^{K_ω}`, with `K_ω = H ∩ ωKω⁻¹`. The twist is trivial on the compact
group `K_ω`. Let `φ_ω` be the function of `renardSpace` supported on `HωK` with
`φ_ω(xωk) = δ_{H\G}(x)`. For `K`-fixed `h` and `f` one gets
`ν(φ) = Σ_ω c_ω h(ω)(f(ω))` with `c_ω = ν(φ_ω)`.

Every `c_ω` is nonzero. Right translation by `ω` carries `φ_ω` to the corresponding function
at the trivial coset for `ωKω⁻¹`. For a normal open subgroup `L` of a compact open `K′`, the
function for `K′` is a sum of `n ≥ 1` right translates of the function for `L`. So all these
values are positive rational multiples of each other. They span `renardSpace` by
translation. Hence if one of them vanished, `ν` would be `0`.

By the I.4.1 Lemma, `W̃^{K_ω} = (W^{K_ω})^*`. So the pairing identifies
`Ind_H^G(W̃)^K` with `(ind_H^G(W ⊗ δ)^K)^* = (ind_H^G(W ⊗ δ)~)^K` for every `K`, and the map
is bijective.

## Remaining obligations

The proof is a separate obligation. It does not need the published
`InvariantFunctionalStatement`, since the argument above uses only that `ν` is invariant and
nonzero.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.HarmonicAnalysis.HomogeneousFunctions` | `relativeModular`, `renardSpace`, `rightAction` |
| `Langlands.Representation.Induction.Definitions` | `smoothInduced`, `compactInduced`, `SmoothFunctions`, `CompactFunctions`, `eval`; through its imports `twist`, `IsSmooth`, `Representation.Equiv` |
| `Langlands.Representation.Smooth.Contragredient.Definitions` | `SmoothDual`, `smoothContragredient`, `smoothDualPairing` |
