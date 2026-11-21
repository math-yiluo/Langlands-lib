# The bound (19) of Lapid's Lemma 10 for smooth wave packets, from four premises

Module `Langlands.Global.LocalWavePacketNormBoundReduction` states and proves
`Langlands.Global.LocalWavePacketNormBoundReductionStatement`:

`LocalWavePacketInnerProductStatement → IntertwiningSquareIntegrableExpansionStatement →
IntertwiningImaginaryUnitarityStatement → InducedInnerProductGramStatement →
LocalWavePacketNormBoundStatement`.

The theorem `Langlands.Global.localWavePacketNormBoundReduction` proves it. The
conclusion `LocalWavePacketNormBoundStatement` (module
`Langlands.Global.AdelicLocalWavePacketStatement`) is the bound (19) of Lapid's
Lemma 10 for wave packets in Lapid's space `W_P`. In the data of that statement
it asserts that `Ω(P, P) = weylParameterSet p l p l π` is finite, that
`y ↦ Θ(y.out)` is in `L²(G(F) \ G(𝔸), μG)`, and that
`∫ ‖Θ(y.out)‖² dμG ≤ |Ω(P, P)| · ∫ Re (φ(x), φ(x))_P d(spectralMeasure n)(x)`
with `φ(x) = ∑ j, c j x · v j`.

The four premises are published propositions:

- (A) `LocalWavePacketInnerProductStatement` (module
  `Langlands.Global.AdelicLocalWavePacketStatement`): Lapid's Proposition 2,
  formula (4), for smooth wave packets regular near their support.
- (E) `IntertwiningSquareIntegrableExpansionStatement` (module
  `Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement`):
  `M(w, λ)φ = ∑ i, coeff i λ • ψ i` with `ψ i ∈ A^2_Q` and coefficients
  meromorphic with a domain containing `i(X^*(P) ⊗ ℝ)`.
- (U) `IntertwiningImaginaryUnitarityStatement` (module
  `Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement`):
  unitarity of `M(w, λ)` on the imaginary axis, in the form of a Gram identity.
- (G) `InducedInnerProductGramStatement` (module
  `Langlands.Global.AdelicInducedInnerProductGramStatement`): positivity of
  `(·,·)_P` on finite families in `A^2_P`, in Gram form.

The module proves the implication only; none of the four premises is proved
here or in the Library at the time of writing. The sesquilinearity of
`(·,·)_P` (`InducedInnerProductSesquilinearStatement`) is not a premise: the
proof derives the finite expansions it needs from the published integrability
theorem `inducedInnerProductIntegrable` and the published
`AdelicGroupPoints.inducedInnerProduct_sum_sum`. The finiteness of `Ω(P, P)`
and the invariance of the spectral measure under `Ω(P, P)` are proved in
`Langlands.Global.AdelicSelfWeylParameters` (a helper module of the same
candidate).

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF, PDF
page = printed page + 9):

- §2, p.312: for `λ ∈ i𝔞_P^*`, `M(w, λ)` is unitary.
- §3, p.314: `W_P`, the norm (3) `‖φ‖²_* = ∫ ‖φ(λ)‖²_P dλ`, `Θ_φ`,
  Proposition 2 and formula (4).
- §8, p.329: Lemma 10, the bound (19) `‖Θ_φ‖² ≤ |Ω| ‖φ‖²_*`, and its proof,
  which uses (4) for `φ_n ∈ W_P` to show that `Θ_{φ_n}` is a Cauchy sequence.

Lapid gives no details for the bound (19) on `W_P`. The derivation implemented
here is the standard one: (4) with `P' = P`, `φ' = φ` expresses `‖Θ_φ‖²` as a
sum over `s ∈ Ω(P, P)` of `∫ (M(s, λ)φ(λ), φ(sλ))_P dλ`. Each term is at most
`‖φ‖²_*` by Cauchy–Schwarz for `(·,·)_P`, the unitarity of `M(s, λ)` and the
invariance of `dλ` under `λ ↦ sλ`. The constant is `|Ω(P, P)|`, the sharper
form of Lapid's `|Ω|` explained in the Markdown of
`AdelicBoundedWavePacketStatement`.

## Helper lemmas (namespace `Langlands.Global.LocalWavePacketNormBound`)

- `two_mul_re_cross_le`: let `Q` be a matrix indexed by `Ia ⊕ Ib` whose Gram
  form `z ↦ ∑ a, ∑ b, z a · conj (z b) · Q a b` is nonnegative (in the order of
  `ℂ`). Then for `u : Ia → ℂ`, `v : Ib → ℂ`,
  `2 Re B ≤ Re A + Re C`, where `B = ∑ u a · conj (v b) · Q (inl a) (inr b)` is
  the mixed term and `A`, `C` are the two diagonal terms. Proof: expand the
  form at `(s u, t v)`. The vector `(u, -v)` gives
  `Re A + Re C - Re B - Re B' ≥ 0`, with `B'` the other mixed term. The vector
  `(u, i v)` has a real form value, which gives `Re B = Re B'`. This replaces
  Cauchy–Schwarz and needs no positivity of the weight `β`.
- `gram_nonneg_of_fin`: positivity of a Gram form on families indexed by
  `Fin m` gives positivity on families indexed by any finite type
  (reindexing by `Fintype.equivFin`).
- `sum_fin_dite_eq`: padding a sum over `Fin k` by zeros to `Fin m`, `k ≤ m`,
  does not change it.
- `isMeromorphicInCoordinatesOn_inter_biInter`: meromorphy in coordinates
  survives a finite intersection with domains that preserve it.
- `continuous_mul_of_eq_zero`: `f · g` is continuous if `f` is continuous and
  zero off a closed set `S`, and `g` is continuous on an open `V ⊇ S`.
- `spectralMeasure_const_ne_top`, `integrable_of_continuous_of_eq_zero`: a
  continuous function vanishing off a compact set is integrable for Lebesgue
  measure and for `spectralMeasure n = (2π)^{-n} dx`.
- `exists_transported_weight`: the signed-weight version of the published
  `exists_transported_coordinates` (module
  `Langlands.Global.AdelicImaginaryIntertwiningExistence`). If
  `x ↦ e'⁻¹(L(e x))` preserves Lebesgue measure, then `e'' = L ∘ e` is a
  coordinate system and `β''(y) = β'(ρ y)` (with `ρ` the transpose of the
  matrix of the inverse coordinate change, `|det ρ| = 1`) is continuous,
  compactly supported, of integral `1`, and
  `β''(coordinates of H in e'') = β'(coordinates of H in e')` for every
  `H`. The proof is the published one without the nonnegativity clause.
- `Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication`: a compatible root
  presentation and a geometric unipotent radical `n` make
  `subgroupMultiplication l n` an isomorphism. The published theorem applies over the underlying field.

## The proof of `localWavePacketNormBoundReduction`

Fix the data of `LocalWavePacketNormBoundStatement` and write
`(·,·)_P = inducedInnerProduct K hK.isCompact p l μM e β`,
`λ(x) = imaginaryParameter F P (e x)` and
`y_t(x) = e⁻¹(realWeylParameter l (cw t) π (e x))`.

1. **Sesquilinearity.** For finite families in `A^2_P`, `(·,·)_P` expands as
   a double sum: `inducedInnerProduct_sum_sum`, with the integrability of every
   pair from the published `inducedInnerProductIntegrable`.
2. **Enumeration of `Ω(P, P)`.** `T` is the subtype of
   `weylParameterSet p l p l π`, finite by `finite_weylParameterSet_self`.
   For each `t` a Weyl conjugation `(w t, cw t)` with
   `weylParameter l (cw t) π = t` is chosen. This enumeration is injective and
   surjective, as (A) requires.
3. **Expansions.** For each `t` and `j`, (E) (with `Q = P`, `q = p`,
   `iV = iU`, `l' = l`, `r' = r`, `π' = π`, the multiplication isomorphism from
   `Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication`) gives finitely many
   `ψ' t j i ∈ A^2_P` and coefficients `cf t j i` with a domain `Dd t j`. They
   are padded to the common length `m = ∑ t, ∑ j, kk t j`: the extra vectors
   are `v j` and the extra coefficients are `0`. The expansion of
   `M(w_t, λ) v j` is unchanged (`sum_fin_dite_eq`). The published
   `exists_domain_of_isMeromorphicInCoordinatesOn` enlarges each `Dd t j` to
   `Dd' t j`. The common domain is `DM = D ∩ ⋂_{t, j} Dd' t j`. It contains
   `{λ(x) | x ∈ S}`, and every padded coefficient is meromorphic on it: the
   zero coefficient through `isMeromorphicInCoordinatesOn_zero_of` applied to
   `E j · 1`, the others through `isMeromorphicInCoordinatesOn_inter_of` and
   `isMeromorphicInCoordinatesOn_inter_biInter`.
4. **Unitarity.** `measurePreserving_realWeylParameter` shows that `y_t`
   preserves Lebesgue measure. `exists_transported_weight` then gives
   coordinates `e''_t = w_t ∘ e` and a weight `β''_t` with the same inner
   product `(·,·)_P` (unfold `inducedInnerProduct`). (U), with `P' = P` and
   `μM' = μM`, gives coefficients `coeff''` and a domain `DM''_t ⊇ i𝔞_P^*`.
   On `DM ∩ DM''_t` they give the same functions `∑ i, coeff'' · ψ`, and for
   every imaginary `λ` they satisfy the Gram identity
   `∑ i, ∑ i', coeff'' t j i λ · conj (coeff'' t j' i' λ) · (ψ t j i, ψ t j' i')_P = (v j, v j')_P`.
5. **Formula (4).** (A), with `P' = P` and all primed data equal to the
   unprimed data, gives `MemLp` of `Θ` and
   `∫ Θ · conj Θ dμG = ∫ ∑ t, B_t(x) dx`, where
   `B_t(x) = ∑ j, ∑ i, ∑ j', c j x · coeff t j i (λ(x)) · conj (c j' (y_t x)) · (ψ t j i, v j')_P`.
6. **Pointwise bound.** Let
   `N(x) = ∑ j, ∑ j', c j x · conj (c j' x) · (v j, v j')_P`, which is
   `(φ(x), φ(x))_P` by step 1. For each `t` and `x`,
   `2 Re B_t(x) ≤ Re N(x) + Re N(y_t x)`. Apply `two_mul_re_cross_le` to the
   family `(ψ t j i)_{(j, i)} ⊔ (v j')_{j'}`, which is positive by (G) and
   `gram_nonneg_of_fin`, with
   `u (j, i) = c j x · coeff t j i (λ(x))` and `v j' = c j' (y_t x)`. Its
   mixed term is `B_t(x)` and its second diagonal term is `N(y_t x)`. Its
   first diagonal term is `N(x)`, by step 1 and step 4. Write it as
   `(Ψ, Ψ)_P` with `Ψ = ∑ (j, i), u (j, i) · ψ t j i`. For `x ∈ S`, `Ψ` equals
   the same combination with `coeff''`, because `λ(x) ∈ DM ∩ DM''_t`; for
   `x ∉ S` every `c j x` is `0`. Expanding again and using the Gram identity
   at `λ(x)` gives `N(x)`.
7. **Integration.** Every `x ↦ c j x · coeff t j i (λ(x))` is continuous
   (`continuous_mul_of_eq_zero`, with continuity of the coefficients on the
   open set `{x | λ(x) ∈ DM}` from
   `BoundedWavePacket.isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn`)
   and vanishes off the compact `S`. So `B_t` and `N` are integrable
   (`integrable_of_continuous_of_eq_zero`), and so is `N ∘ y_t`
   (`integrable_comp_spectralMeasure`). By the published
   `integral_comp_spectralMeasure`, `∫ N(y_t x) dx = ∫ N(x) dx`. Integrating
   step 6 gives `∫ Re B_t ≤ ∫ Re N` for every `t`.
8. **Conclusion.** `Θ · conj Θ = ‖Θ‖²` pointwise, so
   `∫ ‖Θ‖² dμG = Re ∫ ∑ t, B_t = ∑ t, ∫ Re B_t ≤ |T| · ∫ Re N`. Here
   `|T| = Nat.card (weylParameterSet p l p l π)`, and
   `N(x) = (φ(x), φ(x))_P`. The first two conjuncts are
   `finite_weylParameterSet_self` and the `MemLp` clause of (A).

## Scope

The theorem is a reduction. The exact target `LocalWavePacketNormBoundStatement`
follows once (A), (E), (U) and (G) are proved. Their proof tasks are Task 8058
(A), the task for `IntertwiningSquareIntegrableExpansionStatement` (E), Task
5682 (U) and the task for `InducedInnerProductGramStatement` (G).
