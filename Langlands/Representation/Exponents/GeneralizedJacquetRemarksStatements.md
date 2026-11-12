# Renard VI.9.1: the bound `b ≤ c(G, K)` and Remarks 1–3 after the Proposition (statements)

Module `Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements`.
Universe parameters `u, v`. The module contains two **statements**, both `Prop`-valued
definitions; it proves nothing:

- `Langlands.Aubert.General.RationalPointFamily.GeneralizedJacquetRemarksStatement`;
- `Langlands.Aubert.General.RepresentedParabolic.GeneralizedJacquetContractingRangeStatement`.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.9.1, printed pp.195–198 / PDF pp.201–204, and VI.9.2, printed
pp.198–199 / PDF pp.204–205.

Fix `P = MN` with split component `A`, a compact open `K` with an Iwahori decomposition
relative to `P`, and `t ∈ C_A^{++}`. `A` acts on `V^K` by `a_{t,K} = e_K ∗ δ_t ∗ e_K`.
The Proposition of VI.9.1 says `A^b` is stable for a constant `b = b(G, K)`, and sets
`V^K_0 = ker A^b`, `V^K_* = Im A^b`, so `V^K = V^K_0 ⊕ V^K_*`. It ends:

> De plus la constante `b` peut être choisie plus petite ou égale que la constante
> `c(G, K)` du théorème d'admissibilité uniforme VI.2.3.

After its proof come three remarks:

> *Remarques.* 1. La décomposition `V^K = V^K_0 ⊕ V^K_*` ne dépend pas du choix de `t`
> dans `C_A^{++}`. Si `(π, V)` est admissible, on retrouve la décomposition de la
> proposition VI.6.1. — 2. Il existe des sous-groupes ouverts compacts `C` de `N` et `C̄`
> de `N̄` tels que pour tout `(π, V) ∈ M(G)`, `V^K_0 = V^K ∩ ker e_C`,
> `V^K_* = e_K ∗ e_{C̄} · V`. — 3. Il existe `ε > 0` tel que pour tout `t ∈ A^+(ε)`,
> `V^K_0 = ker π(a_{t,K})`, `V^K_* = Im π(a_{t,K})`.

Here `A^+(ε) = {a ∈ A_M | |α(a)|_F < ε, α ∈ Δ(P)}` (V.3.22.1, printed p.117 / PDF p.123). The
published VI.9.1 statements (`UniformCompressionStabilizationStatement`,
`GeneralizedJacquetLemmaStatement`) state the Proposition and the Theorem. Their
Markdown records the bound and Remarks 1–3 as not stated. This unit states them.
The admissible case of Remark 1 is the published and proved VI.6.1 statement
`StandardCanonicalSectionStatement`.

## The objects

`GeneralizedJacquetRemarksStatement` uses the setting of the published VI.9.1
statements. `k` is a nonarchimedean local field with `T2Space` and `G` is connected
reductive. `rationalPoints G` carries the canonical topology `pointTopology`, with
`LocallyCompactSpace` and `NonarchimedeanGroup` binders. `χ` is a cocharacter of `G`.
`N`, `M` and `N̄` are the rational points of the dynamic radical of `χ`, its
centralizer, and the dynamic radical of the inverse cocharacter. `K` is a compact open
subgroup. `g` is an `M`-central element with `Jacquet.IsIwahoriContraction K N M N̄ g`.
These hypotheses give `g ∈ M`, the factorization `K = (K ∩ N̄)(K ∩ M)(K ∩ N)`, and the
contraction and exhaustion properties. The element `g` plays the role of Renard's `t`,
as in the published statements. For a smooth representation `ρ` on `V`:

- `A` is `Jacquet.compressedAction ρ hρ K hK g`, the endomorphism `v ↦ e_K(ρ(g) v)` of
  `V^K = fixedVectors ρ K`;
- `V^K_0` is `Jacquet.powerKernelSup` (`⨆ r, ker A^r`) and `V^K_*` is
  `Jacquet.stableImage` (`⨅ r, range A^r`). The published Proposition identifies them
  with `ker A^b` and `Im A^b`.

`GeneralizedJacquetContractingRangeStatement` uses the setting of the published VI.9.6
pairing statement `LeviJacquetOppositePairingStatement`. `P = MN` and `P̄ = MN̄` are
actual rational parabolics with the same rational Levi and `P(F) ∩ P̄(F) = M(F)`. `K`
is compact open, and `t₀ ∈ G(F)` is `M(F)`-central with
`Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F) t₀`. `a : A → M` is a split component
with a compatible `ParabolicRootPresentation`. `Δ(P)` is the set of restrictions of the
simple relative roots outside the presentation's `J`, exactly as in the VI.9.6
statement. An element `t ∈ A(F)` acts through `rationalPoints.map (a ≫ m ≫ p)`, and
`characterNorm k A α t` is the published normalized norm `|α(t)|_F`.

## The statements

`GeneralizedJacquetRemarksStatement` asserts, after the binders above, the
conjunction of three clauses.

1. **Bound.** For every `c : ℕ` such that `dim V^K ≤ c` for every irreducible
   `A : SmoothRep.{0, u, v} ℂ G(F)`, and for every smooth `ρ` on `V : Type v` and every
   `s ≥ c`: `stableImage = range (A^s)` and `powerKernelSup = ker (A^s)`.
2. **Remark 1.** For every other `M`-central `g'` with
   `IsIwahoriContraction K N M N̄ g'` and every smooth `ρ`, `g'` and `g` have the same
   `powerKernelSup` and the same `stableImage`.
3. **Remark 2.** There are compact open subgroups `C` of `N` and `C̄` of `N̄`, in their
   subspace topologies, such that for every smooth `ρ`:
   `powerKernelSup = ker (e_C restricted to V^K)` and
   `stableImage` (as a submodule of `V`) `= range (e_K ∘ e_{C̄})`. Here
   `e_C = Compact.averageMap (ρ ∘ N.subtype) _ C _`, the normalized average over `C` of
   the restriction of `ρ` to `N` (smooth by the published `isSmooth_comp`). `e_{C̄}` is
   defined in the same way, and `e_K = Compact.averageMap ρ hρ K hK`.

`GeneralizedJacquetContractingRangeStatement` asserts, after its binders, that there
is a real `ε > 0` such that for every `t ∈ A(F)` with `|α(t)|_F < ε` for all
`α ∈ Δ(P)`, and every smooth `ρ` on `V : Type v`:

- `powerKernelSup ρ hρ K hK t₀ = ker (compressedAction ρ hρ K hK t)`, and
- `stableImage ρ hρ K hK t₀ = range (compressedAction ρ hρ K hK t)`.

## Formalization choices

- **Which `b`.** Renard's `c(G, K)` is the constant of VI.2.3: `dim V^K ≤ c(G, K)` for
  every irreducible `V`. The statement allows every such bound `c`, so it applies to
  Renard's constant. "`b` can be chosen `≤ c`" is stated as "`c` is a valid exponent".
  These are equivalent: if `A^b` is stable then the power kernels and ranges are
  constant from `b` on, hence from `c` on. Renard's proof (VI.9.2) uses only
  `dim i_Q^G(W ⊗ χ)^K ≤ c` for the irreducible members of a family, so any bound on
  the irreducible representations works. As in the published Proposition statement,
  stability is expressed by constancy of the power kernels and ranges.
- **Remark 1 for all contracting elements.** In the dynamic setting, `t ∈ C_A^{++}` is
  replaced by every `M`-central element satisfying the published Iwahori contraction
  conditions. This is the class of elements that the published VI.9.1 statements use
  in place of `t`.
- **`ker e_C` on `V^K`.** Renard writes `V^K ∩ ker e_C`. The statement takes the kernel
  of `e_C` restricted to `V^K`, as a submodule of `V^K`, the type of `powerKernelSup`.
  `e_K ∗ e_{C̄} · V` is the range of `e_K ∘ e_{C̄}` on `V`, and `stableImage` is pushed
  into `V` by the inclusion of `V^K`.
- **Remark 3: kernel and image of `π(a_{t,K})`.** The kernel is taken on `V^K`, as in
  Renard's proof ("`ker π(a_{t,K})|_{V^K}`"). The image is taken on `V^K`. Since
  `π(a_{t,K}) = e_K π(t) e_K` and `e_K V = V^K`, it equals the image on `V`.
- **Remark 3: `A^+(ε)`.** The statement uses all of `A(F)` with `|α(t)|_F < ε` for
  `α ∈ Δ(P)`, which is (V.3.22.1). The published VI.9.6 statement uses this remark for
  `t ∈ C_A^+(ε)`, a subset of `A^+(ε)`. There is no condition `|α(t)|_F ≤ 1`, as in
  V.3.22.1. Since `ε` is existential, this changes nothing.
- **Remark 3: which decomposition.** `V^K_0` and `V^K_*` are those of the compressed
  action of `t₀`. `K` and `t₀` are fixed before `A`, the presentation and `ε`, and `ε`
  is chosen before the representation. In Renard, `ε` comes from the uniform `C` and
  `C̄` of Remark 2, so it does not depend on `(π, V)`.
- **Two settings.** Remarks 1–2 and the bound are stated in the dynamic setting of the
  published Proposition. `A^+(ε)` needs the split component `A_M` and `Δ(P)`, which the
  dynamic setting does not provide. So Remark 3 is stated in the actual-parabolic
  setting with root presentations, as in the published VI.9.6 statement that uses it.
  For a parabolic without a compatible presentation, Remark 3 asserts nothing.

## Not stated

The Proposition also says that the localization of `V^K` at `A` is `(V^K_*, A|V^K_*)`.
That claim is not stated here. It is the localization part of Appendix C.II applied to
the published Proposition; see the Library's C.II audit `notes/renard/stable-quotients.md`.
The two lemmas of VI.9.1 have proved Library counterparts in
`Langlands.Representation.Jacquet.CompressionLocalization`
(`fixedJacquetMap_kernel_locally_nilpotent`, `localizationEquivOfKernelExhaustion`).
The second sentence of Remark 1 (the admissible case gives the decomposition of VI.6.1)
is the published and proved `StandardCanonicalSectionStatement`.

## Why the statements are true

The proof is a separate obligation. Renard's route:

- **Bound** (VI.9.2): for the induced progenerator `V_Π = i_Q^G(Π_1)`, the
  specializations `i_Q^G(ρ ⊗ χ)` are irreducible for `χ` outside a Zariski-closed set
  (VI.8.5), so `A^c` kills their `K`-fixed vectors in the nilpotent part. A
  generic-freeness argument over the coordinate ring (VI.8.4) shows that `A^c` kills
  `(V_Π)^K_0`. Then C.II(iv) applies. The extension to all smooth `V` (VI.9.3) keeps the
  same exponent, by exact sequences and C.II(ii)–(iii).
- **Remark 1:** `V^K_0 = V^K ∩ V(N)` by the first lemma of VI.9.1, which does not depend
  on `t`. For two contracting elements `s, t`, `a_{s,K} a_{t,K} = a_{st,K}` (V.5.3).
  So `Im A_{st}^b ⊆ Im A_s^b ∩ Im A_t^b`, and complements of `V^K_0` contained in
  one another are equal.
- **Remark 2:** choose `C ⊇ t^{-b} K_N t^b` and `C̄ ⊇ t^b K_{N̄} t^{-b}`. Then (VI.9.1.5)
  gives `π(a_{t^b,K}) v = δ_{t^b} ∗ e_{N_b} v`, and III.2.9 gives the converse.
- **Remark 3:** by V.5.2 there is `ε` with `C ⊆ t^{-1} K_N t` and
  `C̄ ⊆ t K_{N̄} t^{-1}` for `t ∈ A^+(ε)`. Then `π(a_{t,K}) v = δ_t ∗ e_{t^{-1} K_N t} v`
  on `V^K`, and Remark 2 identifies the kernel and the image.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Exponents.UniformCompressionStabilizationStatement` | dynamic setting, `compressedAction`, `stableImage`, `powerKernelSup`, `IsIwahoriContraction` |
| `Langlands.Representation.Exponents.LeviJacquetOppositePairingStatement` | actual parabolic setting, `pointImage`, `ParabolicRootPresentation`, `CocharacterUniformizer.characterNorm`, `SmoothRep.IsIrreducible` (through its imports) |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | `isSmooth_comp` |
| `Langlands.Representation.Compact.Definitions` | `Compact.averageMap` |
