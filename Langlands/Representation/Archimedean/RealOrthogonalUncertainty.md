# An uncertainty principle for two block rotations of `O(3)`

Module `Langlands.Representation.Archimedean.RealOrthogonalUncertainty` proves
`Langlands.Archimedean.RealOrthogonalBlockUncertaintyStatement` (module
`Langlands.Representation.Archimedean.RealOrthogonalUncertaintyStatement`, by Worker 763) as the
theorem

```lean
theorem Langlands.Archimedean.RealOrthogonalUncertainty.realOrthogonalBlockUncertainty :
    RealOrthogonalBlockUncertaintyStatement
```

## Statement proved

Let `r_0(θ) = blockRotation 3 0 θ` and `r_1(θ) = blockRotation 3 1 θ`, and let `{p, q} = {0, 1}`
and `n' < n`. Let `f : GL_3(ℝ) → ℂ` be continuous and right `O(3)`-finite. Suppose that at every
`g ∈ O(3)` the block Fourier coefficients `blockFourierCoefficient 3 p j f g` vanish for `|j| < n`,
and `blockFourierCoefficient 3 q j f g` vanish for `|j| ≥ n'`. Then `f g = 0` for every `g ∈ O(3)`.

## Provenance

This is an internal lemma for the `GL_3(ℝ)` standard-module filtration tasks (Tasks 7133 and
7134). It is used to prove that composites of block Fourier multiplier maps are injective. The
proof follows the `sl₂` route sketched in the Markdown of the statement, together with the parity
reduction suggested there. No literature statement is formalized.

## Proof

### Abstract part (section `Abstract`)

Let `W` be a complex vector space.

* `IsModeDecomposition a π S`: the operators `π m` (`m ∈ ℤ`) are orthogonal idempotents that sum
  to the identity, `π m = 0` for `m ∉ S` (a finite set), and `a π_m = i m π_m`. So `π m` is the
  projection onto the `i m`-eigenspace of `a`; we call it the `a`-mode `m`.
* Suppose `[a, b] = c`, `[b, c] = a` and `[c, a] = b` (the relations of `so(3)`; here
  `[x, y] = x y - y x`). Then `E₊ = b - i c` and `E₋ = b + i c` satisfy `[a, E₊] = i E₊` and
  `[a, E₋] = -i E₋`. So `E₊` raises the `a`-modes by one and `E₋` lowers them by one
  (`proj_apply_of_lie`). Also `[E₊, E₋] = 2i a`, so `((2i) a, E₋, -E₊)` is an `sl₂`-triple in
  the sense of Mathlib's `IsSl2Triple`.
* `proj_eq_zero_of_pos` (`W` finite-dimensional). Let the `a`-modes of `v` all have absolute value
  at least `n`, and let `Q(-i b) v = 0` for a nonzero polynomial `Q` of degree `d < n`. If some
  positive mode of `v` is nonzero, let `k ≥ n` be the lowest one (`Nat.find`). Write
  `b = (E₊ + E₋)/2`. By induction on `e ≤ d`, the modes `m` of `b^e v` with
  `-n + e < m < k - e` vanish, and its mode `k - e` is `2^{-e} E₋^e π_k v`. Since
  `-n + d < k - d`, the mode `k - d` of `b^e v` vanishes for `e < d`. So the mode `k - d` of
  `Q(-i b) v = 0` is a nonzero multiple of `E₋^d π_k v`, and `E₋^d π_k v = 0`. Hence there is an `e < d` with
  `E₋^e π_k v ≠ 0` and `E₋^{e+1} π_k v = 0`. This vector is primitive for the `sl₂`-triple, with
  `(2i) a`-eigenvalue `-2(k - e) < 0`. This contradicts
  `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`, which makes the eigenvalue a natural number.
* `eq_zero_of_finite_modes`. Suppose in addition that `b` has a mode decomposition and the
  `b`-modes of `v` lie in a finite set `T` with `|T| < n`. Then `Q = ∏_{j ∈ T} (X - j)` kills `v`
  through `-i b` (`aeval_prod_apply_eq_zero`). Apply `proj_eq_zero_of_pos` to `(a, b, c)` for the
  positive modes, and to `(-a, b, -c)` with the reflected decomposition (`reflect`) for the
  negative modes. Mode `0` vanishes by hypothesis, so `v = 0`.
* `eq_zero_of_parity`. Let `σ` satisfy `π_m σ = σ π_{-m}` and multiply the `b`-mode `j` by
  `(-1)^j`. Let the `a`-modes of `v` be at least `n` in absolute value and its `b`-modes smaller
  than `n'` in absolute value, with `n' < n`. The vectors `v ± σ v` keep the hypothesis on the
  `a`-modes. Their `b`-modes lie among the integers of `(-n', n')` of one parity, at most `n'` of
  them (`card_filter_parity_le`). So both vanish by `eq_zero_of_finite_modes`, and so does `v`.
* `relations_swap` exchanges the roles of two generators in the relations; it is used for
  `(p, q) = (1, 0)`.

### Analytic part (section `Analytic`)

Write `K3 = Matrix.unitaryGroup (Fin 3) ℝ` and `rot p θ` for `r_p(θ)` in `K3`.

* **Function space.** `RealKTypeCount.degreeLE 3 N` (from the module `RealKTypeCount`) is the
  finite-dimensional space of functions on `O(3)` given by polynomials of degree at most `N` in
  the matrix entries. It is stable under left and right translation by `O(3)`. Orbits
  `θ ↦ w(r_p(θ) x)` of its elements are trigonometric polynomials (`orb_mem_trigPoly`), so they
  are continuous and `2π`-periodic.
* **Mode projections.** `projFun p m w x = (2π)⁻¹ ∫₀^{2π} w(r_p(θ) x) e^{-imθ} dθ`. It preserves
  `degreeLE 3 N` (`projFun_mem`). Proof: by `exists_sum_of_separating`, the functional
  `u ↦ ∫ u(r_p(θ)) e^{-imθ} dθ` on `degreeLE 3 N` is a combination of finitely many point
  evaluations. Applied to the right translates of `w`, this writes `projFun p m w` as a
  combination of left translates of `w`. The projections `proj N hp m` are orthogonal
  idempotents that sum to the identity (Fourier expansion of a trigonometric polynomial). With
  `gen N hp = Σ_m i m · proj N hp m`, this gives `isModeDecomposition`.
* **Derivatives and derivations.** The derivative at `0` of `θ ↦ w(r_p(θ) x)` is `(gen N hp w)(x)`
  (`hasDerivAt_orb_gen`). The derivative along `r_p`, `derFun p`, maps the algebra `P3` of
  polynomial functions on `O(3)` (`OrthogonalFinitePolynomial.polynomialFunctions 3`) to itself and
  is a derivation `der hp` of `P3`. `HasMatrix δ X` says that `δ` sends the entry function
  `x ↦ x_{ik}` to `x ↦ Σ_l X_{il} x_{lk}`. `der hp` has the matrix `rotationGenerator 3 p`
  (`hasMatrix_der`). The commutator of derivations with matrices `X, X'` has the matrix
  `X' X - X X'` (`hasMatrix_lie`). Two derivations with the same matrix are equal, because the
  entry functions generate `P3` (`eq_of_hasMatrix`).
* **Relations.** The matrix identities `rotationGenerator_lie_one` and `rotationGenerator_lie_two`
  hold by computation. Through `incl : degreeLE 3 N → P3`, which intertwines `gen N hp` with
  `der hp`, they give the relations `gen_relations` of the operators `g_p = gen N _` on
  `degreeLE 3 N`: with `c = g_0 g_1 - g_1 g_0`, `g_1 c - c g_1 = g_0` and `c g_0 - g_0 c = g_1`.
  `exists_relations` puts them in the form `[a, b] = c`, `[b, c] = a`, `[c, a] = b` with
  `a = g_p`, `b = g_q`, for `(p, q) = (0, 1)` and `(1, 0)`.
* **Parity operator.** `flipOp N q` is left translation by `r_q(π)`. Since
  `r_q(π) r_p(θ) = r_p(-θ) r_q(π)` (`rot_pi_mul_rot`), it reverses the `r_p`-modes
  (`proj_flipOp`). It multiplies the `r_q`-mode `j` by `e^{ijπ} = (-1)^j` (`proj_flipOp_self`).

### Conclusion (`realOrthogonalBlockUncertainty`)

The restriction of `f` to `O(3)` has a finite-dimensional translate span, because `f` is right
`O(3)`-finite. It is continuous, so it is a polynomial function
(`OrthogonalFinitePolynomial.mem_polynomialFunctions_of_finiteDimensional`) and lies in some
`degreeLE 3 N` (`RealKTypeCount.exists_mem_degreeLE`); call this element `v`. At `x ∈ O(3)`,
`blockFourierCoefficient 3 r m f x` is `2π` times the value at `x` of the mode `m` of `v` along
`r_r` (`blockFourierCoefficient_eq_coeff`). So the hypotheses say that the `r_p`-modes of `v` with
`|m| < n` vanish and the `r_q`-modes with `|j| ≥ n'` vanish. `eq_zero_of_parity`, with
`σ = flipOp N q` and the relations of `exists_relations`, gives `v = 0`. Evaluating at `g` gives
`f g = 0`.
