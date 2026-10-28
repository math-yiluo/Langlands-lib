# Maximal layers of a dual-detected character quotient: proof

Worker 868 wrote this proof and its explanation.

The module proves

```
Langlands.dualCharacterMaximalLayer.{uG,uH,uV} :
  Langlands.DualCharacterMaximalLayerStatement.{uG,uH,uV}
```

The statement is the published pair
`Langlands/Representation/Exponents/DualCharacterMaximalLayerStatement.lean` and
`.md`, and this module imports it unchanged. The theorem is closed: it takes no
hypotheses beyond those of the statement, and it keeps the universes of the
acting group `G`, the central parameter group `H` and the carrier `V`
independent. It uses no `sorry` and no new axioms.

Notation, as in the statement Markdown: `T = commutativeTranspose (ρ.comp ι)`,
`E = DualCharacterQuotient.dualSpace ρ ι χ`, `N_c = T c - (χ c : ℂ) • 1` on the
dual, and `D_c = DualCharacterQuotient.defect ρ ι hι χ c` on the quotient.

The proof avoids logarithms. Its key input is an algebraic lemma in a
commutative `ℂ`-algebra, proved by downward induction over the ideals spanned
by monomials of large degree. A Vandermonde argument then separates the binomial
terms. The helper results live in the namespace
`Langlands.DualCharacterMaximalLayer`.

## 1. Vandermonde extraction (`section Vandermonde`)

`coeff_eq_zero_of_eval_nat K d c h`: let `K` be a field of characteristic
zero, `A` a `K`-algebra (a ring, not necessarily commutative), and
`c : Fin (d + 1) → A`. If `∑_{p ≤ d} n^p · c p = 0` for `n = 0, …, d`, then
`c = 0`.

The Vandermonde matrix `M` of the nodes `0, …, d` in `K` has nonzero
determinant (`Matrix.det_vandermonde_ne_zero_iff`). The nodes are distinct
because `ℕ → K` is injective in characteristic zero, so `M` is invertible. The
hypothesis says `M.map (algebraMap K A) *ᵥ c = 0`. Multiplying by the mapped
inverse (`Matrix.nonsing_inv_mul`, `Matrix.map_mul`, `Matrix.mulVec_mulVec`)
gives `c = 0`.

## 2. Monomial filtration (`section Layers`)

Fix a commutative ring `A` and elements `x y : A`. Let `𝓕 k` (local notation)
be the ideal spanned by the monomials `x^i * y^j` with `k ≤ i + j`.

- `monomial_mem`, `layer_antitone`, `layer_mul_le`, `mul_mem_layer`,
  `pow_mem_layer`, `x_mem_layer_one`, `y_mem_layer_one`. These give the
  filtration properties: `𝓕` is antitone, `𝓕 k * 𝓕 l ≤ 𝓕 (k + l)` (via
  `Ideal.span_mul_span`), and `s ∈ 𝓕 1` implies `s^k ∈ 𝓕 k`.
- `one_add_pow_sub_mem`: `(1 + x)^n - 1 - n x ∈ 𝓕 2`, by induction on `n`.
- `shifted_sub_linear_mem`: `((1 + x)^n (1 + y) - 1) - (n x + y) ∈ 𝓕 2`.
- `linear_mem`, `shifted_mem`: `n x + y` and `z_n := (1 + x)^n (1 + y) - 1`
  both lie in `𝓕 1`.
- `shifted_pow_sub_linear_pow_mem`: for `0 < d`,
  `z_n^d - (n x + y)^d ∈ 𝓕 (d + 1)`. The proof writes the difference as
  `(∑_{i<d} z_n^i (n x + y)^(d-1-i)) * (z_n - (n x + y))` (`geom_sum₂_mul`).
  The sum lies in `𝓕 (d - 1)` and the second factor lies in `𝓕 2`.

Now assume `K` is a field of characteristic zero, `A` is a `K`-algebra,
`0 < d`, `x^d = 0` and `z_n^d = 0` for every natural `n`.

- `layer_eq_bot_of_succ` (downward step). If `d ≤ m` and `𝓕 (m + 1) = ⊥`, then
  `𝓕 m = ⊥`. Multiplying the previous membership by `y^(m-d) ∈ 𝓕 (m - d)`
  lands in `𝓕 (m + 1) = ⊥`, and `z_n^d = 0`, so
  `y^(m-d) (n x + y)^d = 0` for every `n`. Expanding with `add_pow`
  gives `∑_{p ≤ d} n^p · (choose d p · x^p y^(d-p) y^(m-d)) = 0` for all `n`.
  By Section 1, each coefficient vanishes. Multiplying by
  `algebraMap K A (choose d p)⁻¹`, which exists because `choose d p ≠ 0` in
  `K`, then gives `x^p y^(d-p) y^(m-d) = 0` for `p ≤ d`. Now take a generating
  monomial `x^i y^j` of `𝓕 m`:
  - if `i + j > m`, it lies in `𝓕 (m + 1) = ⊥`;
  - if `i + j = m` and `d ≤ i`, it is killed by `x^d = 0`;
  - if `i + j = m` and `i < d`, then `j = (d - i) + (m - d)`, so it is one of
    the vanishing products above.
- `layer_eq_bot_of_le`. If `x^d = y^d = 0` and `2d ≤ m`, then `𝓕 m = ⊥`,
  because each generator has `d ≤ i` or `d ≤ j`.
- `layer_eq_bot`. Under the standing assumptions, `𝓕 d = ⊥`. Here
  `y^d = z_0^d = 0`. Induction on `t` proves `𝓕 m = ⊥` whenever `d ≤ m` and
  `2d ≤ m + t`. The base case is `layer_eq_bot_of_le` and the inductive step
  is `layer_eq_bot_of_succ`. Taking `t = m = d` finishes.
- `pow_pred_mul_eq_zero`. Under the same assumptions, `x^(d-1) * y = 0`,
  because this monomial of degree `d` lies in `𝓕 d = ⊥`.

This is where characteristic zero and the group law enter. Commuting operators
with `x^d = y^d = 0` alone do not suffice, as the counterexample in the
statement Markdown shows. The lemma also needs `z_n^d = 0` for all `n`, and it
needs the binomial coefficients `choose d p` and the Vandermonde determinant
to be invertible.

## 3. Mixed defects for a commutative action (`section Generic`)

`defect_pow_pred_mul_eq_zero σ χ hd hnil a c`: let `E` be any complex vector
space, `σ : H →* Module.End ℂ E` with `H` commutative, and `χ : H →* ℂˣ`. If
`(σ b - χ b • 1)^d = 0` for every `b` and `0 < d`, then

```
(σ a - χ a • 1)^(d-1) * (σ c - χ c • 1) = 0.
```

The operators `σ b` commute pairwise because `H` is commutative. So the
subalgebra `Algebra.adjoin ℂ (Set.range σ)` is commutative
(`Algebra.isMulCommutative_adjoin`), and the algebraic lemma applies there.
Set `u b = χ(b)⁻¹ • σ b` in that subalgebra. Then:

- `(u b - 1)^d = χ(b)^(-d) • (σ b - χ b • 1)^d = 0`;
- `u a ^ n * u c = u (a^n c)`, because `σ` and `χ` are homomorphisms.

Take `x = u a - 1` and `y = u c - 1`. Then
`(1 + x)^n (1 + y) - 1 = u (a^n c) - 1`, whose `d`-th power vanishes. So
`pow_pred_mul_eq_zero` (with `K = ℂ`) gives `x^(d-1) y = 0`. Back in
`Module.End ℂ E` this equation reads
`(χ a)^(-(d-1)) (χ c)^(-1) • (σ a - χ a)^(d-1) (σ c - χ c) = 0`. The scalar is
nonzero, so the operator product vanishes.

## 4. Transfer to the generalized dual space (`section Application`)

`transpose_defect_pow_pred_mul_eq_zero`: assume `0 < d` and
`(N_b)^d φ = 0` for every `b : H` and every `φ ∈ E`. Then

```
(N_a)^(d-1) (N_c φ) = 0   for all a, c : H and φ ∈ E.
```

The lemma applies Section 3 to the restricted representation
`σ = (dualSpace ρ ι χ).toRepresentation` on the submodule `E`. By induction on
`k`, the values of `(σ b - χ b • 1)^k ψ` are `(N_b)^k ψ.val`. Hence the bound
gives `(σ b - χ b • 1)^d = 0`, and the operator identity of Section 3,
evaluated at `⟨φ, hφ⟩`, gives the claim.

## 5. The main theorem (`dualCharacterMaximalLayer`)

The proof introduces all data and the hypothesis `hidx : index = d`. First,
`hidx.le`, `commutativeCharacterNilpotenceIndex_le_iff` and
`mem_commutativeCharacterSpace` give the uniform bound `(N_b)^d φ = 0` for all
`b : H` and `φ ∈ E`.

**Nonzero image.** Since the index equals `d > d - 1`, it is not at most
`d - 1`. By `commutativeCharacterNilpotenceIndex_le_iff` and
`SetLike.not_le_iff_exists`, some `φ ∈ E` lies outside
`commutativeCharacterSpace T χ (d - 1)`. Unfolding with
`mem_commutativeCharacterSpace` gives `a : H` with `(N_a)^(d-1) φ ≠ 0`,
hence `v : V` with `((N_a)^(d-1) φ) v ≠ 0`.

The witness is `defectRangeMap ρ ι hι χ a (d - 1) v`. Suppose it were zero.
Then `defectRangeInclusion_map` would give `D_a^(d-1) (quotientMap v) = 0`, and
`evaluation_defect_pow_quotientMap` at `⟨φ, hφ⟩` would give
`((N_a)^(d-1) φ) v = 0`, a contradiction. So `nontrivial_of_ne` shows that the
carrier is `Nontrivial`.

**Scalar action.** Fix `a`, `c` and a vector `w` of the range. By
`mem_defectRange` and `quotientMap_surjective`, `w = D_a^(d-1) (quotientMap v)`.
By `defect_pow_quotientMap`, this is the quotient image of
`(ρ (ι a) - χ a)^(d-1) v`. The goal `ρ (ι c) w = χ c • w` is rewritten as
`D_c w = 0` (`sub_eq_zero`, `defect_apply`). By dual separation
(`eq_zero_iff`) it suffices that every `φ ∈ E` evaluates to zero there.
`evaluation_defect_pow_quotientMap` turns that value into
`(N_c φ) ((ρ (ι a) - χ a)^(d-1) v)`. Then
`commutativeTranspose_defect_pow_apply` turns it into
`((N_a)^(d-1) (N_c φ)) v`, which vanishes by Section 4.

The proof does not assume that the image of `D_a^(d-1)` already lies in the
simultaneous eigenspace; this is exactly what Section 4 establishes.

## Scope and provenance

The theorem adds no hypothesis to the published statement. It uses neither
topology nor finiteness, and it uses the published quotient and range
representations themselves. It does not invert or conjugate `χ`. Only Mathlib and
the API imported by the statement module (`DualCharacterQuotient`,
`DualJacquet`, `NilpotenceIndex`) are used. Nothing depends on any GL support,
criticality or tempered-refinement statement.

This proof fills in the step that Silberger, *Introduction to harmonic analysis
on reductive p-adic groups* (1979), registered as
`silberger-1979-harmonic-analysis`, asserts with "Clearly" in the proof of
Corollary 2.4.2 (printed p.92, PDF p.98). The source gives no argument, and
the statement Markdown suggests a route through logarithms. This proof uses a
different, elementary route: the filtration by monomial ideals in Section 2
replaces the logarithm, and only binomial expansion and an invertible
Vandermonde matrix over `ℂ` are needed.
