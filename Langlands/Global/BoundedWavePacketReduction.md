# Lapid's Lemma 10 from its smooth case

Module `Langlands.Global.BoundedWavePacketReduction` states and proves
`Langlands.Global.BoundedWavePacketLocalSufficiencyStatement`, the
implication

`LocalWavePacketInnerProductStatement → LocalWavePacketNormBoundStatement →
InducedInnerProductSesquilinearStatement → LeviProjectionExistenceStatement →
WavePacketIwasawaCompatibleMeasureExistenceStatement → BoundedWavePacketStatement`.

The premises are stated in `AdelicLocalWavePacketStatement` (see its
Markdown); `BoundedWavePacketStatement` is the published statement of Lapid
2011, Lemma 10 (p.329, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`). This is a
conditional result: none of the five premises is proved, so
`BoundedWavePacketStatement` stays unproved.

## Statement

`BoundedWavePacketLocalSufficiencyStatement : Prop` is the implication above.
Its proof is `boundedWavePacketLocalSufficiency := boundedWavePacket_of_local`.

Provenance (derived): Lapid's proof of Lemma 10 derives the lemma from
Proposition 2 and (19) for smooth packets `φ_n ∈ W_P` approximating `φ`. The
first two premises are these two facts for `W_P`. The last three are
properties of the Library's formalization that the argument uses tacitly:
`(·,·)_P` is an inner product on `A^2_P`, and the target's first part gives a
Levi projection and an Iwasawa-compatible measure only for the second
parabolic `P'`, while (19) for `P` needs them for `P`.

## Proofs

The auxiliary lemmas below (domains, `spectralMeasure_lt_top`,
`exists_coefficient_approximation`, `ae_tendsto_of_restrict`,
`exists_weight`, `measurable_bounded_of_contDiff`) are in the namespace
`Langlands.Global.BoundedWavePacket`; the main theorems are in
`Langlands.Global`.

### Domains (`isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn`, `exists_open_domain`)

If `f` is meromorphic in coordinates on `V = X^*(P) ⊗ ℂ` with domain `D`, take
the coordinates `ec : ℂ^d ≃ V` of a basis. `IsMeromorphicOn` makes
`ec⁻¹(D)` open and `f ∘ ec` holomorphic, hence continuous, on it. For a
real-linear `L : ℝⁿ → V` (here `x ↦ i e(x)`), `x ↦ ec⁻¹(L x)` is linear on a
finite-dimensional space, hence continuous. So `{x | L x ∈ D}` is open and
`f ∘ L` is continuous on it. `exists_open_domain` does this for a family
`f i`: the common domain `D' = D` if the family is nonempty, and
`D' = univ` otherwise (then the meromorphy hypotheses are vacuous). So
degenerate index sets (`k = 0`, no Weyl elements, `m = 0`) need no separate
case.

### Auxiliary lemmas

- `spectralMeasure_lt_top`: `spectralMeasure n = (2π)^{-n} • volume` is
  finite on compact sets.
- `exists_coefficient_approximation`: from the hypotheses on the `c j`
  (measurable, bounded, zero outside the compact `S ⊆ interior N`) and a
  finite measure `ν`, a common bound `A ≥ 0` and smooth coefficients
  `cs m j`, zero outside `N`, bounded by `A`, with `cs m j → c j`
  `ν`-a.e. for all `j` (`exists_seq_smooth_tendsto_ae` for each `j`, with
  the bound `C = ∑ j, max (C_j) 0`).
- `ae_tendsto_of_restrict`: convergence a.e. for `σ` restricted to `N`
  extends to `σ`-a.e. convergence, since outside `N ⊇ S` all functions are
  `0`.
- `exists_weight`: the normalized smooth bump `ContDiffBump.normed` is a
  continuous compactly supported weight `β` with `∫ β = 1`.

### The norm bound (`boundedWavePacketNormBound_of_local`)

From `LocalWavePacketNormBoundStatement` and
`InducedInnerProductSesquilinearStatement`:

1. With `L x = i e(x)` and the family `(j, g) ↦ (λ ↦ E j λ g)`,
   `exists_open_domain` gives `D' ⊇ D` with `{x | L x ∈ D'}` open,
   the `E j` meromorphic with domain `D'`, and `x ↦ E j (i e(x)) g`
   continuous there. It contains `S`, so `exists_compact_between` gives a
   compact `N` with `S ⊆ interior N` and `N ⊆ {x | L x ∈ D'}` (Lapid's
   "fixed compact neighborhood of `C` on which `E_P(ψ, ·)` is regular").
2. `exists_coefficient_approximation` with `ν = σ|_N` gives smooth `cs m`
   (Lapid's `φ_n`, with values in `V`, uniformly bounded, supported in `N`).
3. `InducedInnerProductSesquilinearStatement` (with the given `π`) rewrites
   `(φ(x), φ(x))_P` as `gramForm Gm (c x)` with
   `Gm j j' = (v j, v j')_P`.
4. For smooth `d` vanishing outside `N`, `LocalWavePacketNormBoundStatement`
   with `S := N` and `D := D'` gives finiteness of `Ω(P, P)`, `L²`
   membership, and `∫ ‖Θ_d‖² ≤ |Ω(P, P)| ∫ Re (gramForm Gm (d x)) dx`. This is
   the hypothesis `HB` of `packet_core`.
5. `packet_core` gives `Θ ∈ L²` and the bound for `c`; rewriting back with
   step 3 gives the conclusion. Finiteness comes from step 4 with `d = 0`.

### The inner product formula (`boundedWavePacketInnerProduct_of_local`)

From all five premises:

1. `LeviProjectionExistenceStatement` and
   `WavePacketIwasawaCompatibleMeasureExistenceStatement` give `π : P → M` with
   `l ≫ π = 𝟙` and an Iwasawa-compatible Haar measure `μM`; `exists_weight`
   gives `β`. These are used only to apply the norm bound to `P`.
2. Domains as above: `D₁ ⊇ D` for the `E j`, `DM₁ ⊇ DM` for the
   `coeff t j i`, and `D₁' ⊇ D'` for the `E' j`. Compact `N ⊆ {L ∈ D₁} ∩ {L ∈ DM₁}`
   with `S ⊆ interior N`, and `N' ⊆ {L' ∈ D₁'}` with
   `S' ⊆ interior N'`.
3. The maps `L_t x = e'⁻¹(realWeylParameter l (cw t) π' (e x))` are linear,
   hence continuous. Approximate `c` with `ν = σ|_N`, and `c'` with the finite
   measure `ν' = σ'|_{N'} + ∑ t, (L_t)_*(σ|_N)`. Then `cs' m → c'` a.e. for
   `σ'|_{N'}` and, for each `t`, `cs' m ∘ L_t → c' ∘ L_t` a.e. for `σ|_N`
   (`ae_of_ae_map`). No invertibility of `L_t` is needed.
4. `packet_core` for `P` (with `π`, `μM`, `β`, the norm-bound premise and the
   sesquilinearity, both applied with `π`) and for `P'` (with the given `π'`,
   `μM'`, `β'`) gives
   `Θ, Θ' ∈ L²` and `L²` convergence `Θ_{cs m} → Θ`, `Θ'_{cs' m} → Θ'`. These
   are the first two conclusions.
5. For each `m`, `LocalWavePacketInnerProductStatement` with
   `c := cs m`, `S := N`, `D := D₁`, `c' := cs' m`, `S' := N'`,
   `D' := D₁'`, `DM := DM₁` and the other data unchanged gives (4) for the
   smooth packets.
6. The left side converges to `∫ Θ · conj Θ'` (`tendsto_integral_mul_conj`).
   The right side converges to the right side of the target by
   `tendsto_integral_of_bdd_of_zero_off`. The integrand vanishes outside
   `N`, is continuous on `N`, and is bounded there by
   `∑ A · max (C_{tji}) 0 · A' · ‖(ψ t j i, v' j')_{P'}‖`, where `C_{tji}`
   bounds `coeff t j i (i e(x))` on `N`. It converges a.e. by step 3. Lapid:
   "Taking the limit in the identity (4) for `φ_n` we will obtain the Lemma."
   Uniqueness of limits gives the identity.

`boundedWavePacket_of_local` combines both parts.

### The premises are special cases of the target

`measurable_bounded_of_contDiff`: a smooth function vanishing outside a
compact set is measurable and bounded. Hence
`localWavePacketInnerProduct_of_bounded` and
`localWavePacketNormBound_of_bounded`: the two parts of
`BoundedWavePacketStatement` imply `LocalWavePacketInnerProductStatement` and
`LocalWavePacketNormBoundStatement`. These two premises are therefore no
stronger than the target.

## Scope

Lapid's polarization step (the case `φ' = φ` first) is not used: the cross
formula is passed to the limit directly. Unitarity of `M(w, λ)`
(`IntertwiningImaginaryUnitarityStatement`) and finiteness of `Ω(P, P)` are
not used here. They enter only through `LocalWavePacketNormBoundStatement`,
whose proof from Proposition 2 needs them.
