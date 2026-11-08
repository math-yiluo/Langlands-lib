# The last ramification group is abelian

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.LastGroupProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.InertiaProof` and
`Langlands.VirtualRepresentation.Weil.Ramification`.

## What the module proves

### Local rings

Let `A` be a commutative local ring with maximal ideal `𝔪`, and let `f, g : A ≃+* A`. Fix
`n : ℕ` and suppose `f x - x ∈ 𝔪^(n+1)` for every `x`, and likewise for `g`.

- `sub_mem_maximalIdeal_pow_of_mem f hf k hk b hb`: for `k ≥ 1` and `b ∈ 𝔪^k`,
  `f b - b ∈ 𝔪^(k+n)`.
- `commutator_sub_mem_maximalIdeal_pow f g hf hg x`: `f (g x) - g (f x) ∈ 𝔪^(2n+1)`.

### Finite extensions

Let `F` be a finite p-adic field with any realization `T : F.TopologicalData`, and let `K` be a
field below it with the usual scalar towers. Write `G_i` for `Padic.lowerRamificationGroup T K i`
and `G^v` for `Padic.upperRamificationGroup T K v`. For `σ, τ` in `F.Carrier ≃ₐ[K] F.Carrier`:

- `integerAutomorphism_mul` and `integerAutomorphism_inv_apply`: the Library integer-ring
  automorphisms are multiplicative and invert correctly.
- `commutator_mem_lowerRamificationGroup`: if `σ, τ ∈ G_n`, then `(τσ)⁻¹(στ) ∈ G_{2n}`.
- `lowerRamificationGroup_commute`: if `n ≥ 1`, `G_{n+1} = ⊥` and `σ, τ ∈ G_n`, then
  `στ = τσ`.
- `exists_gt_commutator_mem_upperRamificationGroup`: if `a > 0` and `σ, τ ∈ G^a`, then
  `(τσ)⁻¹(στ) ∈ G^w` for some `w > a`.
- `upperRamificationGroup_commute`: if `a > 0` and `G^w = ⊥` for every `w > a`, then any two
  elements of `G^a` commute. So the last nontrivial upper ramification group of positive
  index is commutative.

### Absolute and Weil groups

Let `F : PadicField p`, and write `G^v` for `absoluteUpperRamificationGroup F v`.

- `absoluteUpperRightLimit F a` is the one named definition. It is the closed right limit
  `G^{a+}`: the Krull closure of `⨆ (w : ℝ) (_ : a < w), G^w` in
  `Field.absoluteGaloisGroup F.Carrier`. `isClosed_absoluteUpperRightLimit` records that it is
  closed.
- `commutator_mem_closedRightLimit F ha hσ hτ`: if `a > 0` and `σ, τ ∈ G^a`, then
  `(τσ)⁻¹(στ) ∈ absoluteUpperRightLimit F a`. In other words, `G^a / G^{a+}` is commutative.
- `localProjection_commutator_mem_closedRightLimit`: for `x, y` in the Library Weil upper group
  `LocalWeil.Ramification.upperGroup F a` with `a > 0`, the projection
  `Weil.Local.localProjection F ((y x)⁻¹ (x y))` lies in `absoluteUpperRightLimit F a`.

## Sources

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Chapter IV, §2,
Proposition 10 and Lemma 2 (printed p. 70, PDF p. 77): for `s ∈ G_j`, `t ∈ G_i` with
`i, j ≥ 1`, the commutator lies in `G_{i+j+1}`, and by the lemma at least in `G_{i+j}`. The case
used here is `i = j = n`, with the weaker conclusion `G_{2n}`. It is proved differently, by an
ideal-power estimate rather than Serre's uniformizer computation. The upper and absolute forms
are derived assertions, using the upper numbering (IV §3) and the absolute filtration
(IV §3, Remark 1).

The application is Deligne–Henniart (1981), §4.5 (registered as
`deligne-henniart-1981-variation`, printed p. 110, PDF p. 22). There `G` is the quotient
`W/N` of the Weil group `W` by the subgroup `N` of inertia that acts trivially on the
irreducible representation `V`. The image `I/N` of inertia is finite (DH81 §0.5, printed
p. 92), but `G` itself is not finite: since `N ⊆ I`, it still maps onto `W/I ≅ ℤ`. DH81 uses
that `G(α(V))`, the last nonzero ramification group of `G`, is abelian. This module works
instead with the finite Galois quotients `Gal(L/F)` (in the proofs) and with the actual Weil
group through `localProjection` (in the Weil statement). It assumes no finite image of the
whole Weil group. The local-ring lemmas are internal steps.

## Proof (as implemented)

1. **Ideal-power estimate** (`sub_mem_maximalIdeal_pow_of_mem`). Induct on `k ≥ 1`. For
   `k = 1` this is the hypothesis. Since `𝔪^(k+1) = 𝔪^k · 𝔪`, it suffices
   (`Submodule.mul_induction_on`) to treat products `x y` with `x ∈ 𝔪^k`, `y ∈ 𝔪`, and sums.
   For products use
   `f (x y) - x y = f x · (f y - y) + (f x - x) · y`. Here `f x ∈ 𝔪^k` because ring
   isomorphisms preserve powers of the maximal ideal (`ringEquiv_mem_maximalIdeal_pow_iff`), and
   `f y - y ∈ 𝔪^(n+1)`. By the induction hypothesis `f x - x ∈ 𝔪^(k+n)`. Both terms lie in
   `𝔪^(k+1+n)`. Sums are handled by additivity.
2. **Commutator estimate.** Put `a = f x - x` and `b = g x - x`, both in `𝔪^(n+1)`. Then
   `f (g x) - g (f x) = (f b - b) - (g a - a)`, and step 1 with `k = n + 1` puts both terms in
   `𝔪^(2n+1)`.
3. **Lower groups** (`commutator_mem_lowerRamificationGroup`). Membership in `G_i` is
   `integerAutomorphism σ x - x ∈ 𝔪^(i+1)` for every integer `x`
   (`Padic.mem_lowerRamificationGroup`). Apply step 2 to the integer automorphisms of `σ` and
   `τ` at `y`, then apply the integer automorphism of `(τσ)⁻¹`, which preserves `𝔪^(2n+1)`.
   This shows that `(τσ)⁻¹(στ)` moves `y` by `𝔪^(2n+1)`, i.e. lies in `G_{2n}`.
4. **Commutativity** (`lowerRamificationGroup_commute`). For `n ≥ 1`, `G_{2n} ≤ G_{n+1} = ⊥`
   (`lowerRamificationGroup_antitone`), so `(τσ)⁻¹(στ) = 1`.
5. **Upper numbering** (`exists_gt_commutator_mem_upperRamificationGroup`). Let
   `m = ⌈ψ(a)⌉`.
   - Since `ψ(a) > 0` (`herbrandPsi_pos`), `m ≥ 1`, and `G^a = G_m`
     (`upperRamificationGroup_eq_lower`).
   - By continuity of `ψ` there is `w > a` with `ψ(w) < m + 1`. Then `⌈ψ(w)⌉ ≤ m + 1`, so
     `G_{m+1} ≤ G^w` (`lowerRamificationGroupInt_antitone`).
   - Step 3 and `G_{2m} ≤ G_{m+1}` give the claim. `upperRamificationGroup_commute` follows
     because `G^w = ⊥`.
6. **Absolute groups** (`commutator_mem_closedRightLimit`). The right limit is closed, so
   `InertiaProof`'s `iInf_comap_map_absoluteFiniteRestriction` reduces membership to every
   finite Galois `L`. There `AbsoluteProof`'s `absoluteUpperClosedRightImage` identifies the
   image of the right limit with `⨆ (w : ℝ) (_ : a < w), G_L^w`. The restrictions of `σ, τ`
   lie in `G_L^a` (`absoluteUpperRamificationGroup_le_comap`). The restriction of the
   commutator is the commutator of the restrictions, which by step 5 lies in some `G_L^w` with
   `w > a`, hence in the supremum (`le_iSup₂`).
7. **Weil groups.** `localProjection F` is a homomorphism, and the Weil upper group is the
   preimage of the absolute upper group. So step 6 applies to the projections.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
