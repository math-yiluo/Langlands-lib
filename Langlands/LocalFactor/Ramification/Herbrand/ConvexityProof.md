# Star-shapedness of the relative inverse Herbrand function

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof`.

## What the module proves

The main results are the inequalities
`relativeHerbrandPsi E (t * a) ≤ t * relativeHerbrandPsi E a` for `a ≥ 0` and `0 ≤ t ≤ 1`, and
in particular `relativeHerbrandPsi E (a / 2) ≤ relativeHerbrandPsi E a / 2`. This is the
inequality `ψ_{L/K}(α/2) ≤ ψ_{L/K}(α)/2` of Deligne–Henniart 4.8, for the relative inverse
Herbrand function `ψ_{E/F}` of a finite intermediate field (defined in `SubextensionProof`).
Only this star-shaped form of convexity is proved, which is what DH81 uses. Full convexity is
not claimed.

### Ramp sums

`ramp i u = min 1 (max 0 (u - i))` is the Library unit ramp, and `polygon` is the Library
Herbrand polygon.

- `rampSum c N u`, the one named definition, is `∑ i ∈ Finset.range N, c (i + 1) * ramp i u`.
  It is the integral from `0` to `u` of the step function equal to `c(i+1)` on `(i, i+1]`.
- `sum_ramp_eq B`: for `0 ≤ u ≤ B`, `∑ i ∈ Finset.range B, ramp i u = u`.
- `polygon_eq_sum g hbB htail`: suppose `g (i+1) = 1` for all `i ≥ b` and `b ≤ B`. Then for
  `0 ≤ u ≤ B`, `polygon g b u = rampSum (fun i => (g i : ℝ)) B u / g 0`.
- `ramp_sum_ratio_mono a b`: let `a i > 0` and `b i ≥ 0` with
  `b i * a j ≤ b j * a i` for `i ≤ j`, so that `b/a` is nondecreasing. Then for `x ≤ y`,
  `rampSum b N x * rampSum a N y ≤ rampSum b N y * rampSum a N x`. That is, `rampSum b / rampSum a`
  is nondecreasing.

### Lower groups over a subfield

Let `K → E → L` be fields with `Padic p`-algebra structures and scalar towers. Here `L` is a
p-adic field with a realization `T`. Write `g i = Padic.lowerGroupOrder T K i` and
`h i = Padic.lowerGroupOrder T E i`.

- `lowerRamificationGroup_subfield_eq_comap`: the lower group over `E` is the preimage of the
  lower group over `K` under `AlgEquiv.restrictScalarsHom K`.
- `lowerGroupOrder_subfield_mul_relIndex`: `h i` times the relative index of
  `H = (restrictScalarsHom K).range` in the lower group over `K` equals `g i`.
- `lowerGroupOrder_subfield_ratio`: for `i ≤ j`, `h i * g j ≤ h j * g i`.
- `herbrandPhi_eq_sum`: for any base `F'` of `L` and `B` at least the cutoff
  `ramificationCutoff T F'`, `Padic.herbrandPhi T F' u` is `rampSum` of the lower group orders
  over `B`, divided by the order of the group of index `0`, for `0 ≤ u ≤ B`.
- `herbrandPhi_herbrandPsi_mul_le`: for `a ≥ 0` and `0 ≤ t ≤ 1`,
  `φ_{T,E}(ψ_{T,K}(t a)) ≤ t · φ_{T,E}(ψ_{T,K}(a))`.

### The relative index and `ψ_{E/F}`

For `F`, `K`, `Ω`, `M` and `h` as in `SubextensionProof`:

- `relativeIndex_zero`, `relativeIndex_strictMono` and `relativeIndex_continuous`: the relative
  index `relativeIndex F M h` vanishes at `0`, is strictly increasing and is continuous.
- `relativeIndex_mul_le`: `relativeIndex F M h (t * a) ≤ t * relativeIndex F M h a` for
  `a ≥ 0` and `0 ≤ t ≤ 1`.

For `E : FiniteIntermediateExtension F.Carrier`:

- `relativeHerbrandPsi_zero`, `relativeHerbrandPsi_strictMono`,
  `relativeHerbrandPsi_continuous` and `relativeHerbrandPsi_nonneg` (`a ≥ 0` gives
  `0 ≤ ψ_{E/F}(a)`).
- `relativeHerbrandPsi_mul_le` and `relativeHerbrandPsi_half_le`, as stated above.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Chapter IV, §3, printed
  p. 73 (PDF p. 80): the explicit formula for `φ` and Propositions 12 and 13 (`φ` is concave
  and `ψ` convex, both piecewise linear and vanishing at `0`). Remark 2 (printed p. 75,
  PDF p. 82) defines the relative functions of a subextension.
- Deligne–Henniart (1981), §4.8 (registered as `deligne-henniart-1981-variation`, printed
  p. 111, PDF p. 23). There the convexity of `ψ_{L_i/K}` is invoked to obtain
  `ψ_{L_i/K}(α(V)/2) ≤ ψ_{L_i/K}(α(V))/2`.

Serre states concavity of `φ` and convexity of `ψ` only for a Galois extension
(Propositions 12 and 13). For the relative function of a subextension, the needed star-shaped
inequality is derived here from the monotonicity of `[G_i : G_i ∩ H]`. The ramp-sum lemmas are
internal steps.

## Proof (as implemented)

1. **Ramp sums.** `sum_ramp_eq` is by induction on `B`. If `u ≤ B` the new ramp vanishes; if
   `B < u ≤ B + 1` all earlier ramps equal `1` and the new one equals `u - B`. For
   `polygon_eq_sum`, `polygon_of_nonneg` writes the polygon as
   `(u + ∑_{i<b} (g(i+1) - 1) ramp_i(u)) / g 0`. The sum extends to `B` with zero terms
   (`htail`), and `u` is replaced by `∑_{i<B} ramp_i(u)`.
2. **Ratio monotonicity** (`ramp_sum_ratio_mono`). Let `k = ⌈x⌉₊` and `c = b k / a k`.
   - A ramp `ramp_i(x)` is nonzero only when `i < x`, so `i + 1 ≤ k` and `b(i+1) ≤ c a(i+1)`.
     Hence `rampSum b N x ≤ c · rampSum a N x`.
   - A difference `ramp_i(y) - ramp_i(x)` (nonnegative by `ramp_monotone`) is nonzero only when
     `x < i + 1`, so `k ≤ i + 1` and `b(i+1) ≥ c a(i+1)`. Hence the increment of `rampSum b` from
     `x` to `y` is at least `c` times that of `rampSum a`.
   - Writing `rampSum · N y` as the value at `x` plus the increment, the two estimates give
     the cross-multiplied inequality (`nlinarith`).
3. **Orders over a subfield.** Membership of `σ` in the lower group over `E` and of
   `σ.restrictScalars K` in the lower group over `K` are the same condition (`Iff.rfl`).
   - So `h i` is the order of `H ⊓ G_i`, where `G_i` is the lower group over `K`
     (`Subgroup.map_comap_eq` and injectivity).
   - `Subgroup.relIndex_inf_mul_relIndex` with `⊥` gives `|H ⊓ G_i| · [G_i : H ⊓ G_i] = |G_i|`.
   - For `i ≤ j`, `G_j ≤ G_i`, so the relative index decreases
     (`Subgroup.relIndex_le_of_le_right`; the groups are finite). Multiplying out gives
     `h i g j ≤ h j g i`.
4. **Herbrand functions as ramp sums** (`herbrandPhi_eq_sum`). `Padic.herbrandPhi` is the
   Library polygon with cutoff `ramificationCutoff`, and `lowerGroupOrder_tail` gives
   `htail`.
5. **Star-shapedness** (`herbrandPhi_herbrandPsi_mul_le`). If `t a = 0` both sides reduce via
   `ψ(0) = φ(0) = 0` and positivity. Otherwise put `x = ψ_{T,K}(t a)` and `y = ψ_{T,K}(a)`, so
   `0 < x ≤ y`, and choose `B` beyond both cutoffs and `⌈y⌉₊`.
   - By step 4, `t a = φ_{T,K}(x)` and `a = φ_{T,K}(y)` are ramp sums of `g` divided by `g 0`,
     and `φ_{T,E}(x)`, `φ_{T,E}(y)` are ramp sums of `h` divided by `h 0`.
   - Step 2 with the ratio monotonicity of step 3 gives
     `h0 φ_{T,E}(x) · g0 a ≤ h0 φ_{T,E}(y) · g0 t a`. Cancel `h0 g0 a > 0`.
6. **Consequences.** The relative index is `φ_{T,K} ∘ ψ_{T,F}` for the canonical realization
   of `extendFiniteGalois h`. This is step 5 with base `F.Carrier` and subfield `K.Carrier`.
   Monotonicity and continuity come from those of `φ` and `ψ`. `relativeHerbrandPsi E` is the
   relative index of `galoisClosure E`. The half inequality is the case `t = 1/2`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
