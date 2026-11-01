# Künneth detection of products of degree-one Čech cocycles (proof)

Author: Worker 921 (the statement and the Čech product infrastructure are by Worker 274).

This module proves `Langlands.Cohomology.Cech.KunnethDetectionStatement` (module
`Langlands.AlgebraicGeometry.CechKunnethStatement`):

```lean
theorem Langlands.Cohomology.Cech.kunnethDetection : KunnethDetectionStatement.{w, w', u}
```

The universe parameters are in the same order as those of the statement. The proof uses no
`sorry` and no new axioms; it depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The argument is the cochain-level proof sketched in the Markdown of the statement module. It is a
slant product with the functional `l`, composed with the shuffle (Eilenberg–Zilber) paths through
the product cover. The algebraic input is the Library's tensor-product description of sections
of the fibre product over affine opens (`tensorFam`, `tensorFam_bijective`, `tensorFam_tmul`,
`tensorFam_lTensor_resPi`, `tensorFam_rTensor_resPi` in
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.ProductCover`). The operator `L`
and the sign bookkeeping below are a project construction. For comparison, The Stacks Project
proves the Künneth formula over a field in Lemma 0BED (`varieties.tex` line 5442 of the
registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5`, Stacks commit
`a04446e5`). Its proof uses the cup-product map of Čech complexes on the product cover
(equation 0BEE). `L` goes in the opposite direction. It applies `l` in the first factor and
reads cochains on the product cover along shuffle paths. It is written out only for the
cochains the statement needs; the Künneth isomorphism itself is not formalized here.

## Proof

All auxiliary declarations are in namespace `Langlands.Cohomology.Cech.KunnethDetection`.
Throughout, `W = prodCover p₁ p₂ U V` and `O σ b = prodOpen p₁ p₂ (inter U σ) (inter V b)`.

### Combinatorics

- `step s j` is `0` for `j < s` and `1` otherwise. `degen s : Fin (m + 2) → Fin (m + 1)` is the
  degeneracy that repeats `s` (clamped to `m`). `skip k : Fin m → Fin (m + 1)` is the face map
  that omits `k`. `succAbove_eq_skip` identifies `k.succAbove` with `skip k`.
- Lemmas `step_comp_skip_*` and `degen_comp_skip_*` compute the composites of `step` and `degen`
  with face maps, case by case.
- `step_comp_edge_self`, `degen_comp_edge_self`, `step_comp_edge_succAbove` and
  `degen_comp_edge_succAbove` compute their composites with the edges `edge k` of the simplex.
  `fin_two_funext` is the function extensionality for `Fin 2` used in these proofs.
- `shuffle_sum` is the sign identity behind `L_d`. For an additive group `A` and
  `F H : ℕ → ℕ → A`, `Q : ℕ → A` satisfying four index relations, the double sum
  `∑_{s ≤ N} ∑_{k ≤ N + 1} (-1)^(s+k) F s k` equals
  `Q 0 - Q (N + 1) - ∑_{t < N} ∑_{j ≤ N} (-1)^(t+j) H t j`. The proof is by induction on `N`.

### Slant product

- `tensorEquiv W hW` is the additive equivalence
  `(∏_σ Γ(X, inter U σ)) ⊗[R] (∏_{Unit} Γ(Y, W)) ≃ ∏_σ ∏_{Unit} Γ(P, prodOpen (inter U σ) W)`
  for an affine open `W ⊆ Y`. It is `tensorFam` (`σ : Fin 2 → ι`), which is bijective because
  all `inter U σ` and `W` are affine.
- `slant W hW` is the additive map `∏_σ Γ(P, prodOpen (inter U σ) W) → Γ(Y, W)` given by
  `lid ∘ (l ⊗ proj ()) ∘ tensorEquiv⁻¹`.
- `slant_mul`: `slant` sends `σ ↦ p₁^* (x σ) * p₂^* y` to `l x • y`.
- `slant_res`: `slant` commutes with restriction along `W' ≤ W`.
- `slant_coboundary`: if `l` kills Čech coboundaries, then `slant` kills the family
  `σ ↦ G (σ ∘ succAbove 0) - G (σ ∘ succAbove 1)` (restricted) for any family `G` indexed by
  `Fin 1 → ι`. To prove it, write `G` as `tensorFam t` (bijectivity again, using that
  `inter U τ` is affine for `τ : Fin 1 → ι`, by `isAffineOpen_inter_one`). The family is then
  `tensorFam` of `rTensor (r₀ - r₁) t`, and `l ∘ (r₀ - r₁) = l ∘ d = 0`.

### The operator `L`

- `ev e b ε β` is the slant product of `σ ↦ e (j ↦ (σ (ε j), b (β j)))`, restricted to
  `O σ b`. `le_inter_prodCover` supplies the inclusion of opens.
- `ev_d` expands `ev (d e)` as an alternating sum of `ev e` over the faces. `ev_res` moves a
  restriction along `inter V b ≤ inter V (b ∘ θ)` into the index map `β`.
- `L m e b = ∑_{s : Fin (m + 1)} (-1)^s ev e b (step (s + 1)) (degen s)` maps
  `(m + 1)`-cochains on `W` to `m`-cochains on `V`. Its summand `s` evaluates `e` on the shuffle
  path `(σ 0, b 0), …, (σ 0, b s), (σ 1, b s), …, (σ 1, b m)`.
- `L_d`: `L (n + 1) (d c) = -d (L n c)` when `l` kills coboundaries. Both sides are rewritten
  as double sums of `ev c` (`ev_d`, `ev_res`) and compared with `shuffle_sum`. The relations
  `h₁ … h₄` are the `step`/`degen`/`skip` lemmas. The boundary term `Q 0 - Q (n + 2)` is the
  slant of a coboundary in the first factor and vanishes by `slant_coboundary`.

### The product formula

- `res_face_pull_add` computes a face of `p₁^* z + p₂^* y`, restricted to an open `O`, as
  `p₁^* (z f₁) + p₂^* (y f₂)` for the two projected index tuples.
- `appLE_cocycle_const`: the pullback of a `1`-cocycle at a constant pair vanishes
  (`cocycle_apply_const`).
- `res_prod_path`: on the shuffle path turning at `s`, the edge `s` has constant second index
  and every other edge `s.succAbove k` has constant first index. So the restricted product of
  the cocycles `p₁^* z k + p₂^* y k` is
  `p₁^* (z s σ) * p₂^* (prod (y ∘ s.succAbove) b)`.
- `L_prod`: by `slant_mul`, `L (n + 1) (prod w) b = ∑_s (-1)^s l (z s) • prod (y ∘ s.succAbove) b`.
  Since `l (z 0) = 1` and `l (z r.succ) = 0`, this is `prod (Fin.tail y) b`.

### Main theorem

`kunnethDetection`: given `prod w = d c`, take `c' = -L n c`. Then
`d c' = -d (L n c) = L (n + 1) (d c) = L (n + 1) (prod w) = prod (Fin.tail y)`
by `map_neg`, `L_d` and `L_prod`.
