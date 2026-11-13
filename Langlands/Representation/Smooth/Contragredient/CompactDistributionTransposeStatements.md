# Transposes of compactly supported distributions on the contragredient (Renard III.1.6, Lemma): statements

Module `Langlands.Representation.Smooth.Contragredient.CompactDistributionTransposeStatements`.
Namespace `Langlands`. Universe parameters `u` (the group) and `v` (the representation space).
The module contains four **statements**, the `Prop`-valued definitions
`CompactDistributionContragredientTransposeStatement`, `CompactSubgroupHaarTransposeStatement`,
`CompactFixedDualRestrictionStatement` and their conjunction
`ContragredientDistributionLemmaStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The Library already covers these cases of the
III.1.6 Lemma:

- test functions on a group with an inversion-invariant Haar measure
  (`Hecke.integratedAction_smoothDualPairing`, [SmoothTranspose](../../Hecke/SmoothTranspose.md));
- compact open `K` (`SmoothDualCompactFixedDualityStatement`, [CompactDualityStatement](CompactDualityStatement.md)).

Worker 1222's candidate `a5167755` (`Hecke.ContragredientHeckeDualStatement`) gives the
Hecke-algebra case for every t.d. group. No published statement covers the Lemma for
compactly supported distributions `T ∈ ℰ′(G)`, its `e_K` case for compact subgroups that are
not open, or the identification `(V*)^K ≃ (V^K)*` for such `K`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.6, printed p.61 / PDF p.67:

> Lemme. Soit `T ∈ ℰ′(G)`. Pour tout `λ ∈ Ṽ`, pour tout `v ∈ V`, on a :
> `(π̃(Ť) · λ)(v) = λ(π(T) · v)`. En particulier, `(π̃(e_K) · λ)(v) = λ(π(e_K) · v)` pour tout
> sous-groupe compact `K`. Si `λ` est de plus `K`-invariant, on a alors : `λ(v) = λ(π(e_K) · v)`.
> Donc `(V*)^K ≃ (V^K)*`, et si `K` est ouvert, `Ṽ^K = (V*)^K ≃ (V^K)*`.
>
> Démonstration. Rappelons que l'homéomorphisme `g ↦ g⁻¹` de `G` induit l'endomorphisme
> `T ↦ Ť` de `ℰ(G)`. On a :
> `(π̃(Ť) · λ)(v) = ∫_G (π̃(g) · λ)(v) dŤ(g) = ∫_G λ(π(g⁻¹) · v) dŤ(g) = ∫_G λ(π(g) · v) dT(g)
> = λ(π(T) · v)`. Comme `K` est un groupe unimodulaire, on a `ě_K = e_K`, d'où la deuxième
> assertion du lemme. Le reste est une reformulation du lemme I.4.1.

The operators `π(T)` for `T ∈ ℰ′(G)` are those of III.1.3 (printed p.59 / PDF p.65):
`π(T) · v = ⟨T, φ_v⟩ = ∫_G π(g) · v dT(g)` with `φ_v(g) = π(g) · v`.

## Published objects used

- `Distribution.compactlySupported`: the compactly supported distributions `ℰ′(G)`.
- `Distribution.compactSupportFunctional T : LocallyConstant G ℂ →ₗ[ℂ] ℂ`: the pairing
  `⟨T, φ⟩` with locally constant functions (II.1.2).
- `GroupAction.inversionDistributions`: `T ↦ Ť`, the pushforward along `g ↦ g⁻¹`.
- `Distribution.compactSubgroupHaar K hK`: the normalized Haar distribution `e_K` of a compact
  subgroup `K`, with no openness assumption (II.3.11).
- `SmoothDual ρ`, `smoothContragredient ρ` and `smoothDualPairing ρ`: the contragredient
  `(π̃, Ṽ)` and the pairing `⟨ℓ, v⟩ = ℓ(v)`.
- `Representation.dual` (Mathlib): `π*` on `V*`, `(π*(g) m)(v) = m(π(g⁻¹) v)`; `fixedVectors`.

## The statements

Let `G` be a t.d. group (Hausdorff, locally compact, totally disconnected) and `(ρ, V)` a
smooth complex representation. The first two statements take linear maps
`act : ℰ′(G) → End_ℂ(V)` and `act' : ℰ′(G) → End_ℂ(Ṽ)` satisfying the III.1.3
characterization:

- `m(act(T) x) = ⟨T, φ⟩` for every `T`, every `x ∈ V`, every linear form `m` on `V` and every
  locally constant `φ` with `φ(g) = m(ρ(g) x)`;
- the same for `act'`, with `Ṽ`, `ρ̃` and linear forms on `Ṽ`.

**`CompactDistributionContragredientTransposeStatement`.** If `T, Tinv ∈ ℰ′(G)` and `Tinv` is the
inversion of `T`, then `⟨act'(Tinv) ℓ, x⟩ = ℓ(act(T) x)` for all `ℓ ∈ Ṽ` and `x ∈ V`.

**`CompactSubgroupHaarTransposeStatement`.** For every compact subgroup `K` of `G`:

1. `⟨act'(e_K) ℓ, x⟩ = ℓ(act(e_K) x)` for all `ℓ ∈ Ṽ` and `x ∈ V`;
2. `m(act(e_K) x) = m(x)` for every linear form `m` on `V` with `m(ρ(k) y) = m(y)` for all
   `k ∈ K` and `y ∈ V`, and every `x ∈ V`.

**`CompactFixedDualRestrictionStatement`.** For every compact subgroup `K` of `G`, the map
from the `K`-fixed vectors of `ρ.dual`, `(V*)^K`, to `Module.Dual ℂ (V^K)` that restricts a
linear form to the fixed vectors `V^K = fixedVectors ρ K` is bijective.

**`ContragredientDistributionLemmaStatement`** is the conjunction of the three.

## Formalization choices

- **The operators `π(T)`.** The Library has no definition of `π(T)` for `T ∈ ℰ′(G)`. As in
  Worker 1222's III.1.3 candidate `614c7482` (`CompactDistributionActionStatement`), the
  statements characterize `π(T)` by the scalar pairings
  `m(π(T) x) = ⟨T, g ↦ m(π(g) x)⟩`. Linear forms separate the vectors of `V`, so this
  determines `π(T)`; `614c7482` asserts that such linear maps exist. The statements hold for
  every pair `act`, `act'` with this property.
- **`λ`.** The source's functional `λ` is `ℓ` in Lean, where `λ` is reserved.
- **Second assertion.** `ě_K = e_K` holds because `K` is compact. Item 1 states the
  conclusion for `e_K` directly, and item 2 states `λ(v) = λ(π(e_K) v)`. Item 2 is stated for every
  `K`-invariant `m` in the full dual `V*`, which is how the Lemma uses it for `(V*)^K`. The
  condition `m(ρ(k) y) = m(y)` for all `k ∈ K` is `K`-invariance under `π*`, since `K` is a
  group.
- **Fourth assertion.** The isomorphism `(V*)^K ≃ (V^K)*` is stated as bijectivity of the
  restriction map. Its inverse is `μ ↦ μ ∘ π(e_K)`. The case of compact open `K`, together
  with `Ṽ^K = (V*)^K`, is the published `SmoothDualCompactFixedDualityStatement`.
- **Compact subgroups.** `K` is any subgroup with `IsCompact (K : Set G)`. It is then closed,
  because `G` is Hausdorff.

## Why the statements are true

For `x ∈ V`, an open subgroup `K_x` fixes `x`, so `g ↦ m(ρ(g) x)` is locally constant for every
linear form `m`. Take `m` to be evaluation at `x` on `Ṽ`. Then
`⟨act'(Tinv) ℓ, x⟩ = ⟨Ť, g ↦ ℓ(ρ(g⁻¹) x)⟩`. Since `Ť` is the pushforward of `T` along inversion,
this is `⟨T, g ↦ ℓ(ρ(g) x)⟩ = ℓ(act(T) x)`. This is the source's computation.

For a compact subgroup `K`, the Haar measure of `K` is inversion invariant, so `ě_K = e_K`
and item 1 follows. If `m` is `K`-invariant, `g ↦ m(ρ(g) x)` equals `m(x)` on `K`, and `e_K` is a
probability measure supported on `K`, so `m(act(e_K) x) = m(x)`.

For the fourth assertion, `P x = act(e_K) x` is the average of `ρ(k) x` over the finite set
`K/(K ∩ K_x)`, so `P` is a linear projection of `V` onto `V^K` with `P ∘ ρ(k) = P` for
`k ∈ K`. If `m` is `K`-invariant, `m = m ∘ P` by item 2, so `m` is determined by its restriction
to `V^K`. Conversely, for `μ ∈ (V^K)*`, `μ ∘ P` is `K`-invariant and restricts to `μ`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.HarmonicAnalysis.Distribution.Convolution` | `compactlySupported`, `compactSupportFunctional`; through its imports `GroupAction.inversionDistributions` |
| `Langlands.HarmonicAnalysis.Distribution.CompactSubgroup` | `compactSubgroupHaar` |
| `Langlands.Representation.Smooth.Contragredient.Definitions` | `SmoothDual`, `smoothContragredient`, `smoothDualPairing`; through its imports `IsSmooth`, `fixedVectors`, `Representation.dual` |
