# Proof that the coefficient differential squares to zero

The theorem `Langlands.Cohomology.Lie.differentialSquareZero` in
`Langlands/Cohomology/Lie/CoefficientSquareZeroProof.lean` proves the published
proposition `Langlands.Cohomology.Lie.DifferentialSquareZero K L M`. Its
parameters are the same as in that proposition:

- `K : Type u` is a field of characteristic zero.
- `L : Type v` is a `K`-Lie algebra.
- `M : Type w` is a Lie module over `L`, with the `AddCommGroup`, `Module K M`,
  `LieRingModule L M` and `LieModule K L M` structures.

The three universes are independent. Neither `L` nor `M` is assumed finite
dimensional. The proof shows that for every `q : ℕ` the composite
`(differential (q + 1)).comp (differential q)` is the zero linear map. Here
`differential` is the published operator `actionPart q + bracketPart q` from
`Langlands.Cohomology.Lie.CoefficientCochains`; the proof does not replace it
with any other operator. The checker reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Source and route

The operator is the coboundary of Cartan and Eilenberg, *Homological Algebra*
(1956), Chapter XIII §8, printed p.282. The paired Markdown of the statement
records the translation. The source gets square-zero from its resolution
argument (Theorem 7.1, p.280). The Lean proof takes a different route. It is a
self-contained induction on the degree, using interior products and Lie
derivatives ("Cartan calculus"), and it does not use any resolution or
comparison.

## Notation and auxiliary operators

Write `C^q = Cochains K L M q` (alternating `K`-multilinear maps
`L^q → M`) and `d_q = differential q`. For `x : L`:

- **Interior product** `ι_x : C^{n+1} → C^n` (`interiorProduct x n`). This is
  `AlternatingMap.curryLeft`, so `(ι_x f)(z_1,…,z_n) = f(x,z_1,…,z_n)`
  (`interiorProduct_apply`). It is additive in `x`
  (`interiorProduct_add_left`). A cochain of positive degree is determined by
  all of its interior products (`ext_interiorProduct`).
- **Slot derivation** `D_x : C^q → C^q` (`slotDerivation x q`). It is `0` in
  degree `0`. In degree `n+1` it is
  `AlternatingMap.alternatizeUncurryFin (bracketSeed f x)`, so
  `(D_x f)(v_0,…,v_n) = Σ_k (-1)^k f([x,v_k], v_0,…,v̂_k,…,v_n)`
  (`slotDerivation_succ_apply`). This is the same expression that appears
  inside the published `bracketPart`.
- **Lie derivative** `θ_x = x· − D_x` (`lieDerivative x q`), so
  `(θ_x f)(v) = [x, f(v)] − (D_x f)(v)` (`lieDerivative_apply`).

## Elementary lemmas

- `removeNth_zero_vecCons` and `removeNth_succ_vecCons` describe how deleting
  an entry interacts with a tuple whose first entry is given.
- `negOnePow_sum_succ` splits the first term off an alternating sum:
  `Σ_{i<n+1} (-1)^i φ_i = φ_0 − Σ_{j<n} (-1)^j φ_{j+1}`.
- `map_vecCons_vecCons_swap`: swapping the first two arguments of an
  alternating map changes its sign. The proof expands
  `curryLeft_same (a + b)`.
- `slotDerivation_succ_vecCons`:
  `(D_y f)(x, w) = f([y,x], w) + (D_y ι_x f)(w)`. The `k = 0` term gives the
  first summand. In each other term, the bracket and `x` are swapped back by
  `map_vecCons_vecCons_swap`.
- `sum_vecCons_lie_swap`:
  `Σ_j (-1)^j f([z_j, x], z_0,…,ẑ_j,…,z_n) = −(D_x f)(z)`. This follows from
  skew-symmetry of the bracket (`lie_skew`) and linearity of `curryLeft`.

## Identities of Cartan calculus

1. `interiorProduct_lieDerivative`: `ι_y θ_x = θ_x ι_y − ι_{[x,y]}` on
   `C^{n+1}`. Evaluate at `w` and apply `slotDerivation_succ_vecCons`.
2. `lieDerivative_commutator`: `θ_x θ_y − θ_y θ_x = θ_{[x,y]}` on every `C^q`.
   The proof is by induction on `q`.
   - In degree `0`, `D = 0`, and the identity is the module axiom `lie_lie`.
   - In degree `n+1`, apply `ext_interiorProduct` and move `ι_z` inward by
     identity 1. The proof then uses the Leibniz form of Jacobi,
     `[x,[y,z]] = [[x,y],z] + [y,[x,z]]` (`leibniz_lie`), additivity of `ι` in
     its vector, and the induction hypothesis for `ι_z f`. Then `abel` closes
     the goal.
3. `differential_apply_removeNth`:
   `(d_q f)(v) = Σ_i (-1)^i [v_i, f(v without v_i)] − ½ Σ_i (-1)^i (D_{v_i} f)(v without v_i)`.
   - In degree `0` the second sum vanishes, and this is
     `differential_apply_zero`.
   - In positive degree it is the definition `actionPart + bracketPart`,
     unfolded with `alternatizeUncurryFin_apply`. The inner alternating
     uncurrying of `bracketSeed f (v_i)` is `D_{v_i} f` by definition.
     `Fin.removeNth` and the published `omitNth` agree definitionally.
4. Cartan's formula:
   - In degree `0`, `ι_x d_0 f = θ_x f` (`interiorProduct_differential_zero`).
   - In positive degree, `ι_x d_{n+1} f + d_n ι_x f = θ_x f`
     (`interiorProduct_differential_add`).

   For the positive-degree case, evaluate at `z` and expand both
   differentials by identity 3. Then split off the `i = 0` terms with
   `negOnePow_sum_succ`. Set

   - `s = (D_x f)(z)`,
   - `A = Σ_j (-1)^j [z_j, f(x, z without z_j)]`,
   - `B = Σ_j (-1)^j (D_{z_j} ι_x f)(z without z_j)`.

   The action sum of `d_{n+1} f` at `(x,z)` equals `[x, f(z)] − A`. Its slot
   sum equals `s − (−s + B)`, by `slotDerivation_succ_vecCons` and
   `sum_vecCons_lie_swap`. Also `(d_n ι_x f)(z) = A − ½B`. Adding the two
   gives
   `[x,f(z)] − A − ½(s − (−s + B)) + A − ½B = [x,f(z)] − (½s + ½s)`.
   This equals `[x, f(z)] − s = (θ_x f)(z)` because `½s + ½s = s`. Here
   `half_add_half` uses `2 ≠ 0` in `K`, which follows from `CharZero K`. This
   is the only place where characteristic zero is used.

   `interiorProduct_differential_succ` restates the positive-degree formula as
   `ι_x d_{n+1} f = θ_x f − d_n ι_x f`.
5. `lieDerivative_differential`: `θ_x d_q = d_q θ_x`, by induction on `q`. In
   both cases the proof applies `ext_interiorProduct` and rewrites with
   identity 1 and Cartan's formula (identity 4). It then uses identity 2:
   - in degree `0`, `θ_{[x,y]} = θ_x θ_y − θ_y θ_x` closes the goal;
   - in degree `n+1`, it also uses the induction hypothesis
     `θ_x d_n ι_z f = d_n θ_x ι_z f`.
6. `differential_differential`: `d_{q+1} (d_q f) = 0`, by induction on `q`,
   again through `ext_interiorProduct`.
   - In degree `0`:
     `ι_x d_1 d_0 f = θ_x d_0 f − d_0 ι_x d_0 f = θ_x d_0 f − d_0 θ_x f = 0`.
   - In degree `n+1`:
     `ι_x d_{n+2} d_{n+1} f = θ_x d_{n+1} f − d_{n+1}(θ_x f − d_n ι_x f)`.
     This is `0` by the induction hypothesis `d_{n+1} d_n (ι_x f) = 0` and
     identity 5.

Finally, `differentialSquareZero` turns `differential_differential` into the
equality of linear maps with `LinearMap.ext`. Its declared type is exactly
`∀ (K : Type u) (L : Type v) (M : Type w) [Field K] [CharZero K] [LieRing L]
[LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
[LieModule K L M], DifferentialSquareZero K L M`. This was checked by assigning
the unapplied constant to this type.

Authorship: Worker 760.
