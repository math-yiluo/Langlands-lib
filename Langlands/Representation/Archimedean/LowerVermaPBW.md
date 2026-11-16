# Poincaré–Birkhoff–Witt for `U(𝔤𝔩_n(ℂ))` and the lower Verma weight statement

Module `Langlands.Representation.Archimedean.LowerVermaPBW`, namespace
`Langlands.Archimedean.VermaPBW`. It imports the Library module `BGChaseCore` for two small facts about
`M⁻(λ)` (`BGChase.smul_gen`, `BGChase.unitU_smul_gen_diag`).

The main result is `lowerVermaWeight : VermaGL.LowerVermaWeightStatement`. The statement is in
the Library module `LowerVerma`. For every `n` and `λ : Fin n → ℂ`, the generator `gen n λ` of
the lower Verma module `M⁻(λ) = U / (U𝔫⁻ + Σ_p U(E_pp - λ_p))` is nonzero. Moreover, every
`m ∈ M⁻(λ)` with `E_pp • m = λ_p m` for all `p` is a scalar multiple of `gen n λ`
(Bernstein–Gelfand 1980, 1.9(c)). Here `U = U(𝔤𝔩_n(ℂ))`.

Along the way the module builds the Poincaré–Birkhoff–Witt basis of `U` and a family of
linear functionals `Ψ_v` on `U`. These are reused for Duflo's theorem
(`LowerVermaDufloStatement`, a separate task). The proofs follow the standard
Poincaré–Birkhoff–Witt arguments. The Lean route is described below; everything is proved,
with no new axioms.

## 1. Ordered monomials form a basis (generic)

Setting: `L` is a Lie algebra over a field `K` of characteristic zero, with a basis `b` indexed
by a finite type `B` and a list `bs` enumerating `B` without repetition.
`Kostant.orderedMonomial K L b bs α` (Library, `Kostant/OrderedMonomials`) is the ordered
monomial `E^α`.

* `coeff_eq_zero_of_degree_eq`, `linearIndependent_orderedMonomial`: the `E^α` are linearly
  independent. Take a `SymbolData` whose linear symbol sends `b c` to the variable `X c`.
  Suppose a combination `Σ c_α E^α` with all `deg α ≤ N` vanishes. Apply the degree-`N`
  symbol: by the Library lemma `symbol_orderedMonomial` it equals `Σ_{deg α = N} c_α X^α`, so
  those coefficients vanish. Induction on `N` finishes the proof.
* `top_le_span_orderedMonomial`: the `E^α` span `U(L)`. This follows from the Library's
  spanning theorem `degreeFiltration_le_orderedSpan` and `exists_mem_degreeFiltration`.
* `pbwBasis`, `pbwBasis_apply`: the resulting basis.

The Library also proves Poincaré–Birkhoff–Witt in `Langlands.Algebra.OrderedPBWBasis`
(`orderedPBWBasis`), for the monomials `orderedPBWMonomial b` of a basis indexed by `Fin n` in
the natural order. Here the monomials are instead the list-ordered `Kostant.orderedMonomial`,
because the Library's spanning results for them (`degreeFiltration_le_orderedSpan`) apply to
any finite index type, and in particular to the bases of the triangular subalgebras of §3.
Their independence is a short corollary of the Library's `symbol_orderedMonomial`.

List lemmas for `Kostant.expand` (the list of letters of `E^α`): `expand_append`,
`expand_congr`, `expand_map` (expanding along a mapped list), `expand_zero`, `mem_expand`.
`word_append`: the word of a concatenation is the product of the words.

## 2. The ordered basis of `U(𝔤𝔩_n(ℂ))`

* `Idx n = Fin n × Fin n`. `unitE n c` is the matrix unit `E_c = Matrix.single c.1 c.2 1`.
  `UpIdx n` (`p < q`) and `LoIdx n` (`¬ p < q`, diagonal included) are the subtypes of
  strictly upper and lower indices. `upList`, `loList` enumerate them
  (`Finset.univ.toList`). `bsList n` is `upList` followed by `loList`, mapped to `Idx n`
  (`bsList_nodup`, `mem_bsList`).
* `stdB n` is Mathlib's `Matrix.stdBasis`, with `stdB n c = unitE n c` (`stdB_apply`).
  `basisU n` is the Poincaré–Birkhoff–Witt basis of `VermaGL.glU n` for the order `bsList`. Its
  symbol data is the Library's `Kostant.AssocSymbol.symbolData (stdB n)`.
* `W n l` is the word `E_{c₁} ⋯ E_{c_k}` of a list of indices (`W_nil`, `W_cons`, `W_append`).
  `basisU_apply`: `E^α = W(expand bsList α)`. `basisU_apply_split`:
  `E^α = W(upper letters) · W(lower letters)`.

## 3. Triangular subalgebras

Let `P` be a transitive relation on `Fin n`.

* `subalg n P hP` is the Lie subalgebra of matrices `X` with `X i j = 0` whenever `¬ P i j`.
  It is closed under the bracket: if `¬ P i j`, then for every `k` either `¬ P i k` or
  `¬ P k j`.
* `subEquiv` gives the coordinates `X ↦ (X_c)_{P c}`. `subBasis` is the basis of matrix units,
  indexed by `{c // P c.1 c.2}` (`coe_subBasis`: its vectors are the `unitE n c`).
* `subInc : U(𝔰) → U(𝔤𝔩_n)` is induced by the inclusion. It sends the word of a list of basis
  vectors to `W` of the underlying indices (`subInc_ι`, `subInc_word`).
* `subChar μ : U(𝔰) → ℂ` is the algebra map induced by a Lie algebra character `μ : 𝔰 → ℂ`
  (`subChar_ι`). `subChar_word`: on a word it is the product of the values of `μ`.
* `top_le_span_subMonomial`: ordered monomials of `U(𝔰)` span it (Library spanning theorem).

Two instances are used: `nUp n = 𝔫⁺` (`P i j = i < j`, `up_trans`) and
`bLo n = 𝔟⁻` (`P i j = ¬ i < j`, `lo_trans`). Their ordered monomials are `monoUp`, `monoLo`.
They map to `W` of the corresponding indices (`subInc_monoUp`, `subInc_monoLo`).

* `basisU_eq_subInc`: `E^α = subInc(E^{α⁺}) · subInc(E^{α⁻})`, where `α⁺`, `α⁻` are the
  restrictions of `α` (`Finsupp.subtypeDomain`).
* `exists_basisU_eq`: conversely, for ordered monomials `E^β` of `U(𝔫⁺)` and `E^γ` of `U(𝔟⁻)`,
  some `α` has upper letters those of `β` and lower letters those of `γ`.

## 4. The functionals `Ψ_v`

For `v : Idx n → ℂ`, `wt n v α` is the product of `v` over the letters of `E^α`. `Psi n v` is
the linear functional with `Ψ_v(E^α) = wt n v α` (`Basis.constr`; `Psi_basisU`, `Psi_one`).

Assume characters `μ_U` of `𝔫⁺` and `μ_L` of `𝔟⁻` with `μ_U(E_c) = v c` and `μ_L(E_c) = v c`
on the basis vectors (hypotheses `hU`, `hL`).

* `Psi_monoUp_mul_monoLo`: `Ψ_v(subInc(E^β) · subInc(E^γ)) = χ_U(E^β) χ_L(E^γ)`, where
  `χ = subChar μ`. The product is the basis vector `E^α` of `exists_basisU_eq`, and both
  sides are the product of `v` over its letters.
* `Psi_subInc_mul`: `Ψ_v(subInc(u) · subInc(u')) = χ_U(u) χ_L(u')` for all `u ∈ U(𝔫⁺)` and
  `u' ∈ U(𝔟⁻)`. Both sides are linear in each argument and agree on ordered monomials, which
  span (`span_monoUp`, `span_monoLo`, `LinearMap.ext_on_range`). This step is where reordering
  inside `U(𝔫⁺)` and `U(𝔟⁻)` is absorbed.
* `Psi_mul_ι` (right `𝔟⁻`-equivariance): `Ψ_v(u X) = μ_L(X) Ψ_v(u)` for `X ∈ 𝔟⁻`. It is checked
  on `u = E^α` with `basisU_eq_subInc`, since `subInc(u') X = subInc(u' X)`.
* `Psi_ι_mul` (left `𝔫⁺`-equivariance): `Ψ_v(X u) = μ_U(X) Ψ_v(u)` for `X ∈ 𝔫⁺`.

## 5. The characters used

* `muLo n λ : 𝔟⁻ → ℂ`, `X ↦ Σ_p λ_p X_pp`. It kills brackets because the diagonal of `XY` and
  of `YX` agree for lower triangular `X`, `Y`.
* `supCoeff n a p q` is `a_p` if `q = p + 1` and `0` otherwise. `muUp n a : 𝔫⁺ → ℂ` is
  `X ↦ Σ_{p,q} supCoeff n a p q · X_pq`. It kills brackets because a bracket of strictly
  upper triangular matrices vanishes on the superdiagonal.
* `vVal n λ a c` is `supCoeff n a c.1 c.2` on upper indices, `λ_p` on `(p, p)`, and `0` on
  strictly lower indices. `muUp_subBasis` and `muLo_subBasis` give the hypotheses of §4 for
  `v = vVal n λ a`.

## 6. The lower Verma module

* `Psi_mul_unitE_lo`, `Psi_unitE_up_mul`: §4 for single matrix units. `vVal_of_lt`,
  `vVal_diag`: the values of `vVal` on strictly lower and diagonal indices.
* `Psi_mul_mem_lowerVermaIdeal`: `Ψ_{vVal λ a}(u x) = 0` for every `x` in
  `VermaGL.lowerVermaIdeal n λ` and every `u`. This is an induction over the span. On a
  generator `E_pq` (`q < p`) the value is `vVal(p, q) Ψ(u) = 0`. On `E_pp - λ_p` it is
  `λ_p Ψ(u) - λ_p Ψ(u) = 0`.
* `gen_ne_zero`: if `gen = 0` then `1` lies in the ideal, but `Ψ(1) = 1`.
* `mk_eq_smul_gen`: the class of `u` is `u • gen` (the Library's `BGChase.smul_gen`).
* `unitE_lo_smul_gen`: `E_c • gen = vVal(c) gen` for a lower index `c`, because
  `E_c - vVal(c)` lies in the ideal. Iterating this gives `W_lo_smul_gen` for words in lower
  letters, and then `basisU_smul_gen`:
  `E^α • gen = (∏ λ over the lower letters) · W(upper letters) • gen`.
* `lie_diagonal_unitE`, `ι_diagonal_mul`: `[diag(d), E_c] = (d_{c.1} - d_{c.2}) E_c`, and its
  image in `U`. `diagonal_eq_sum`: `diag(d) = Σ_p d_p E_pp`.
* `ι_diagonal_smul`: if `E_pp • m = λ_p m` for all `p`, then `diag(d) • m = (Σ_p d_p λ_p) m`.
  `unitU_smul_gen`: `gen` has weight `λ` (the Library's `BGChase.unitU_smul_gen_diag`).
* `W_eigen`: for every list `l`, `W(l) • gen` is an eigenvector of `diag(d)`, with eigenvalue
  `Σ_p d_p λ_p + Σ_{c ∈ l} (d_{c.1} - d_{c.2})`. The proof is an induction on `l` with
  `ι_diagonal_mul`.

## 7. The weight statement (`lowerVermaWeight`)

Let `dZero n = (0, -1, -2, …)`, `H₀ = diag(dZero)`, `T` the action of `H₀` on `M⁻(λ)` and
`μ₀ = Σ_p dZero_p λ_p`.

* `sum_shift_ne_zero`: for a nonempty list of upper indices `(p, q)`, `p < q`, the sum of
  `dZero_p - dZero_q = q - p` is a positive integer, hence nonzero.
* Every element of `M⁻(λ)` lies in `ℂ · gen ⊔ N`, where `N` is the sum of the eigenspaces of
  `T` for eigenvalues `≠ μ₀`. Write the element as the class of `u ∈ span(E^α)`. By
  `basisU_smul_gen`, `E^α • gen` is a multiple of `W(l) • gen` with `l` the upper letters of
  `E^α`. If `l = []` this is a multiple of `gen`. Otherwise, by `W_eigen` and
  `sum_shift_ne_zero`, it is an eigenvector of `T` with eigenvalue `≠ μ₀`.
* Let `m` have weight `λ`. Write `m = c • gen + z` with `z ∈ N`. Then `T m = μ₀ m` and
  `T gen = μ₀ gen`, so `T z = μ₀ z`. Eigenspaces are independent
  (`Module.End.eigenspaces_iSupIndep`), so `z = 0` and `m = c • gen`.

Together with `gen_ne_zero` this proves `VermaGL.LowerVermaWeightStatement`.

## Provenance

The statement is BG 1.9(c) for the lower Borel subalgebra of `𝔤𝔩_n(ℂ)` (J. N. Bernstein and
S. I. Gelfand, *Tensor products of finite and infinite dimensional representations of
semisimple Lie algebras*, Compositio Math. 41 (1980); literature id
`bernstein-gelfand-1980-tensor-products`). The proof is the standard Poincaré–Birkhoff–Witt
argument, written for this formalization. The independence of ordered monomials uses the
Library's symbol calculus (`Kostant/Symbol`, `Kostant/AssocSymbol`,
`Kostant/OrderedMonomials`). The functional `Ψ_v` replaces the usual identification
`M⁻(λ) ≅ U(𝔫⁺)`.
