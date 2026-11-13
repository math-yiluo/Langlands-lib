# Renard VI.9.1, Remarks 1 and 2, for abstract Iwahori contractions

Author: Worker 167. Module `Langlands.Representation.Jacquet.IwahoriContractionRemarks`,
namespaces `Langlands.Compact` and `Langlands.Jacquet`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.9.1, Remarques 1 and 2 after the Proposition and their proof
(printed pp.197–198 / PDF pp.203–204), together with formula (VI.9.1.5). Registered
source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The module works with an arbitrary topological group `G`, a compact open subgroup `K`,
subgroups `N`, `M`, `Nbar` of `G` and elements satisfying the Library predicate
`Jacquet.IsIwahoriContraction K N M Nbar g`: `g ∈ M`, the Iwahori factorization
`K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`, conjugation by `g` preserving `K ∩ N`, conjugation by
`g⁻¹` preserving `K ∩ M` and `K ∩ Nbar`, exhaustion of `N` and uniform contraction of
`K ∩ Nbar`. For a smooth complex representation `ρ`, `compressedAction ρ hρ K hK g` is
`v ↦ e_K(ρ(g) v)` on `K`-fixed vectors, `powerKernelSup` is the supremum of the kernels
of its powers (Renard's `V^K_0`) and `stableImage` the intersection of the ranges of its
powers (Renard's `V^K_*`); `CompactCompressionSplits` says that they are complementary.
Nothing in this module proves the Proposition of VI.9.1; Remarks 1 and 2 are proved from
its conclusions, which are explicit hypotheses.

## Declarations

### Orbit means and averages (namespace `Langlands.Compact` / `Langlands.Jacquet`)

* `Compact.orbitMean_eq_of_orbit_eq`: orbit means depend only on the orbit set.
* `Compact.orbitMean_eq_apply_of_orbit_eq_image`: if the orbit of `w` under one action is
  the image of a finite orbit of `v` under an injective linear map `f`, then the orbit
  mean of `w` is `f` of the orbit mean of `v`. Proof: rewrite the finite sum along the
  bijection `Equiv.Set.image` and use `Nat.card_image_of_injective`.
* `averageMap_apply_of_mem`: `e_K(ρ(k) v) = e_K(v)` for `k ∈ K`.
* `averageMap_apply_averageMap`: if every `ρ(a) ρ(k) y` with `k ∈ K` equals some
  `ρ(k') ρ(a) y` with `k' ∈ K`, then `e_K(ρ(a) e_K(y)) = e_K(ρ(a) y)`. Proof: expand the
  inner average as a finite mean of `K`-translates of `y`; each term averages to
  `e_K(ρ(a) y)`, and the mean of a constant is that constant.

### Conjugate compact open subgroups

* `conjugateOpenSubgroup K H a : OpenSubgroup H` is `{x ∈ H | a x a⁻¹ ∈ K}`, the preimage
  of `K` under conjugation by `a`, with `mem_conjugateOpenSubgroup` its membership lemma.
* `isCompact_conjugateOpenSubgroup`: it is compact when `K` is compact and `H` is closed
  (preimage of a compact set under a homeomorphism, then under a closed embedding).

For `H = N` and `a = g^s` this is Renard's `t^{-s} K_N t^s`, called `C_s` below; for
`H = Nbar` and `a = g^{-s}` it is `t^s K_{N̄} t^{-s}`, called `C̄_s`.

### Iwahori contractions (namespace `Jacquet.IsIwahoriContraction`)

* `lower_pow`: conjugation by `g^{-s}` preserves `K ∩ Nbar` (induction on `s`).
* `commute_of_central`: an Iwahori contraction `g` commutes with every `g'` central in `M`
  (because `g ∈ M`).
* `mul`: if `g` and `g'` are Iwahori contractions, `g'` is `M`-central and
  `M ≤ normalizer N`, then `g g'` is an Iwahori contraction. The conjugation conditions
  compose; exhaustion uses the exponent `r` for `g'`, normality of `N` under `g'^r` and
  `upper_pow` for `g`; contraction uses the exponent `s` for `g'` after `lower_pow` for
  `g`. Commutation turns `(g g')^r` into `g^r g'^r`.

### Remark 1 (section `RemarkOne`)

* `compressedAction_pow_mul_pow`: `A_{g^r g'^r} = A_g^r A_{g'}^r`, from the Library product
  formula `compressedAction_mul_of_factor` and `IsIwahoriContraction.compressedAction_pow`.
* `stableImage_mul_le`: the stable image of `g g'` is contained in that of `g`, since
  `A_{gg'}^r = A_g^r A_{g'}^r`.
* `eq_of_isCompl_of_le`: in a modular bounded lattice, two complements `s`, `t` of the same
  element with `t ≤ s` are equal.
* `powerKernelSup_eq_of_iwahoriContraction`: the kernel supremum of `g'` equals that of
  `g`, unconditionally. Both are the kernel of the Library map `fixedJacquetMap` to the
  Jacquet module (`powerKernelSup_eq_ker_of_iwahoriContraction`), which does not involve
  the contracting element. This is the Lean form of Renard's identification
  `V^K_0 = V^K ∩ V(N)`.
* `stableImage_eq_of_iwahoriContraction`: if the compressions of `g`, `g'` and `g g'`
  split and both are `M`-central, the stable images of `g` and `g'` agree. Proof: `g g'`
  is an Iwahori contraction with the same kernel supremum as `g` and as `g'`; its stable
  image is a complement of that common kernel supremum contained in the stable image of
  `g` (and, by commutativity, of `g'`), hence equal to both by `eq_of_isCompl_of_le`.

Renard proves Remark 1 through Lemma V.5.3 (`a_{s^n,K} a_{t^n,K} = a_{(st)^n,K}`); the
implemented proof uses the same product formula, but it obtains the kernel half from the
Jacquet-module description and the image half from complementarity.

### Remark 2 (section `RemarkTwo`)

* `apply_apply_eq_of_conj_mem`: if `b⁻¹ k b` fixes `v` then `k` fixes `ρ(b) v`.
* `finite_orbit_inf`: orbits of `K ∩ H` are finite (they lie in `K`-orbits).
* `averageMap_apply_pow_eq` (Renard (VI.9.1.5)): on `K`-fixed vectors,
  `e_K(ρ(g^s) v) = ρ(g^s) e_{C_s}(v)`. Proof: the `K`-orbit of `ρ(g^s) v` is the image under
  `ρ(g^s)` of the `C_s`-orbit of `v`. One inclusion uses the Library lemma
  `exists_upper_translate` (each `k ∈ K` acts on `ρ(g^s) v` like some `u ∈ K ∩ N`), the
  other conjugates `c ∈ C_s` into `K`. Then `orbitMean_eq_apply_of_orbit_eq_image` applies.
* `ker_compressedAction_pow_eq` (kernel half, every power `s`): the kernel of `A_g^s` is the
  kernel of `e_{C_s}` on `K`-fixed vectors, because `ρ(g^s)` is injective.
* `averageMap_lower_eq`: `e_{C̄_s}(w) = ρ(g^s) e_{K ∩ Nbar}(ρ(g^{-s}) w)` (same orbit
  argument).
* `range_compressedAction_pow_eq` (range half, every power `s`, `g` central in `M`): the
  range of `A_g^s`, viewed in `V`, is the range of `e_K ∘ e_{C̄_s}`. Inclusion `⊆`: for
  `z` `K`-fixed, `ρ(g^s) z` is `C̄_s`-fixed, so `A_g^s z = e_K(e_{C̄_s}(ρ(g^s) z))`.
  Inclusion `⊇`: with `y = e_{K ∩ Nbar}(ρ(g^{-s}) w)`, `averageMap_lower_eq` gives
  `e_K e_{C̄_s} w = e_K(ρ(g^s) y)`. Writing `k⁻¹ = l m u` by the Iwahori factorization and
  using that `y` is `K ∩ Nbar`-fixed and that `g^s` commutes with `m`, every
  `ρ(g^s) ρ(k) y` is a `K`-translate of `ρ(g^s) y`; so `averageMap_apply_averageMap`
  gives `e_K(ρ(g^s) y) = e_K(ρ(g^s) e_K y) = A_g^s(e_K y)`.

Renard states Remark 2 for one exponent `b`; here both halves are proved for every power
`s`, and Renard's choice `C ⊇ t^{-b} K_N t^b`, `C̄ ⊇ t^b K_{N̄} t^{-b}` becomes the exact
choice `C = C_b`, `C̄ = C̄_b`. In particular Renard's second step for the image (enlarging
`m`) is not needed.

### Assembly (section `Assembly`)

* `stabilization_of_pow_kill`: if the compression of `g` splits and `A_g^c` kills the
  kernel supremum, then for every `s ≥ c` the range of `A_g^s` is the stable image and
  its kernel is the kernel supremum. Proof: write `v = v₀ + v₁` along the splitting;
  `A_g^s v₀ = 0` and the stable image is `A_g`-invariant
  (`compressedAction_mem_stableImage`), which gives range `⊆` stable image; the reverse
  inclusions are `iInf_le` and `le_iSup`.
* `remarks_of_uniformStabilization`: Remarks 1 and 2 for closed `N`, `Nbar` normalized by
  `M`, from a hypothesis `hU` stating the conclusion of the Proposition of VI.9.1 for every
  `M`-central Iwahori contraction (one exponent `b` for all smooth representations on
  carriers in `Type uV`, the stationary range and kernel equalities for `s ≥ b`, and the
  splitting). Remark 1 applies `hU` to `g`, `g'` and `g g'` (the last is an Iwahori
  contraction by `mul`) and uses the two Remark 1 lemmas. Remark 2 takes `C = C_b`,
  `C̄ = C̄_b` for the exponent `b` of `g` and combines the stationary equalities at `s = b`
  with `ker_compressedAction_pow_eq` and `range_compressedAction_pow_eq`.

`hU` is a hypothesis of the theorem; this module does not prove it.

The averaging-invariance lemma `Langlands.Jacquet.averageMap_apply_of_mem` is reused from `StablePairingProof`. The power-inclusion lemma `Langlands.Jacquet.IsIwahoriContraction.lower_pow` is reused from `Hecke/UniformFixedLevelBounds`. Their duplicate declarations have been removed here; their types and uses are unchanged.
