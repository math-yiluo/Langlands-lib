# Rectangular Fourier inversion at a complex place (Jacquet, Lemma 7.1)

Module `Langlands.Global.RankinSelberg.ComplexGodementFourier`, namespace
`Langlands.Global.RankinSelbergGlobal.ComplexGodementFourier`.

## Statement

`ComplexRectangularFourierInversionStatement` is the complex case of Lemma 7.1 of
H. Jacquet, *Archimedean Rankin-Selberg integrals* (Contemp. Math. 489, 2009; author-posted
version, sha256 `7a11766e…afe`, p. 51). In Jacquet's notation the lemma reads

`∫∫ (w_n.Φ)[v, X] ψ̄(ᵗe_(n-1) X) θ̄_ψ(v) dX dv = ∫∫ (Φ̂.w_(n-1))[v, X] ψ(ᵗe_(n-1) X) θ_ψ(v) dX dv`

for `Φ ∈ S(M((n-1) × n, F))`, with `X ∈ F^(n-1)`, `v ∈ N_(n-1)`, and `[v, X]` the
`(n-1) × n` matrix with the unipotent `v` followed by the column `X`. Here `w_n.Φ` is the right
translate `Y ↦ Φ(Y w_n)`, `Φ̂.w_(n-1)` is the left translate `Y ↦ Φ̂(w_(n-1) Y)`, and
`θ_ψ(v) = ψ(Σ_i v_(i,i+1))`. The extracted text of p. 51 loses the overlines, but the printed page
has them on the left side. Jacquet's Fourier transform (p. 3) is
`F_ψ(Φ)(X) = ∫ Φ(Y) ψ(-Tr(ᵗX Y)) dY` with the self-dual measure.

The Lean statement takes `F = ℂ`, `n - 1 = m = n' + 1` rows (Lean's `n` is `n'`, so `m ≥ 1`), and
`ψ = ψ_a := (complexScaledCharacter a).complex` (abbreviated `psi a`) for an arbitrary
`a ∈ ℂˣ`. Its data are the following.

- `Upper n` is the type of strictly upper triangular positions `(i, j)`, `i < j`, of an
  `(n+1) × (n+1)` matrix. `v : Upper n → ℂ` is the coordinate vector of `v ∈ N_(n+1)`.
- `unip n v` is the upper unipotent matrix with entries `v` above the diagonal, `1` on it and
  `0` below it.
- `blockA n v X` is `[v, X]`: the `(n+1) × (n+2)` matrix whose first `n+1` columns are
  `unip n v` and whose last column is `X : Fin (n+1) → ℂ`.
- `superdiagSum n v X = Σ_(i < n) v_(i,i+1) + X_last`. This is the argument of
  `ψ(ᵗe X) θ_ψ(v)`.
- `piMeasure κ a = Measure.pi (fun _ : κ => (complexSelfDualMeasure a).measure)`. The measure
  `dv dX` is `(piMeasure (Upper n) a).prod (piMeasure (Fin (n+1)) a)`, the product of
  the Library's self-dual measure for `ψ_a` over all coordinates.
- `rectFourier b Φ Y = ∫ Φ X · ψ_b(Σ_(i,j) X_ij Y_ij) dX` with the measure
  `rectangularMeasure (complexSelfDualMeasure b)`. Since `ψ_(-a)(z) = ψ_a(-z)`, Jacquet's
  `Φ̂ = F_ψ Φ` is `rectFourier (-a) Φ`. The self-dual measures of `a` and `-a` coincide.
- `w_k` is the Library's long Weyl element `GeneralLinear.weylLong k ℂ`, used through `.val`.

The statement says that for all `n`, `a` and every Schwartz function
`Φ : 𝓢(Fin (n+1) → Fin (n+2) → ℂ, ℂ)` on the complex `(n+1) × (n+2)` matrices,

`∫ Φ(blockA v X · w_(n+2)) ψ_(-a)(S(v,X)) d(v,X) = ∫ rectFourier (-a) Φ (w_(n+1) · blockA v X) ψ_a(S(v,X)) d(v,X)`,

where `S = superdiagSum`. Since `ψ_(-a) = ψ̄_a`, this is Jacquet's statement for `ψ = ψ_a`. The
integrals are single Bochner integrals over the product space. Fubini turns them into Jacquet's iterated integrals.

Provenance: internal formalization of a published lemma. The only change is the choice of
coordinates (strict upper triangular positions for `v`) and the restriction to `m ≥ 1` rows.
Jacquet's case `n = 1` has zero rows and is trivial.

## Proof (as implemented)

`complexRectangularFourierInversion` proves the statement from `integral_blockA_mul_weylLong_eq`.

**1. Fourier inversion on `ℂ^κ` (section Fourier).** `fourier a G ξ = ∫ G x ψ_a(Σ_k x_k ξ_k)
d(piMeasure κ a)`. It equals the Library's `SchwartzBruhatProof.pairingFourier` for the real
pairing `pairing a w ξ = Tr_(ℂ/ℝ)(a Σ w_k ξ_k)` (`fourier_eq_pairingFourier`).
`exists_realification` gives the data that the Library's `pairingFourier_pairingFourier` and
`exists_schwartz_pairingFourier` need. These are two real-linear isomorphisms
`P = realify κ` and `Q = realify κ ∘ twistPi a` onto `EuclideanSpace ℝ (κ × Fin 2)` with
`pairing a w ξ = ⟪P w, Q ξ⟫`, and image measures `cP • volume`, `cQ • volume` with `cP · cQ = 1`.
Here `realify` sends `x` to `(Re x_k, Im x_k)_k` and preserves volume
(`measurePreserving_realify`, from `Complex.volume_preserving_equiv_pi`, the auxiliary
`measurePreserving_uncurry` and `PiLp.volume_preserving_toLp`). `twist a z = conj(2 a z)` scales
Lebesgue measure by `twistFactor a = |2a|^(-2)` (`map_volume_twist`, from
`Measure.map_linearMap_addHaar_eq_smul_addHaar` and the norm of `ℂ/ℝ`). The constants are
`cP = (2|a|)^|κ|` and `cQ = (2|a| · |2a|^(-2))^|κ|`, which multiply to `1`. Hence:

- `fourier_neg_fourier`: for continuous integrable `G` with integrable `fourier a G`,
  `fourier (-a) (fourier a G) = G` (Fourier inversion with constant exactly `1`).
- `exists_schwartz_fourier`: the Fourier transform of a Schwartz function is (the coercion of)
  a Schwartz function.

**2. Decay (section Decay).** `schwartz_decay` and `schwartz_decay_of_le` give
`‖Ψ w‖ ≤ C (1 + ‖y‖)^(-k)` whenever `‖y‖ ≤ ‖w‖`. `integrable_inv_one_add_norm_pow` shows that
`(1 + ‖y‖)^(-(d+1))` is integrable for any Haar measure in real dimension `d`.
`integrable_of_norm_le_schwartz` combines them: a measurable function bounded by `‖Ψ ∘ g‖` along
a map `g` that does not decrease norms is integrable.

**3. Partial Fourier inversion (section Split).** For a decidable predicate `p` on a finite
index type `ι`, `merge p x z` glues `x` on `{i // p i}` and `z` on `{i // ¬ p i}`
(`MeasurableEquiv.piEquivPiSubtypeProd` inverted). `integral_merge` is the corresponding
measure-preserving change of variables. The main lemma `integral_merge_left_eq` states that for
`Φ ∈ 𝓢(ℂ^ι)`, `α` on the `p`-block and `β` on its complement,

`∫ Φ(merge x β) ψ_(-a)(Σ x_k α_k) dx = ∫ fourier (-a) Φ (merge α y) ψ_a(Σ y_k β_k) dy`.

Its proof sets `G z = ∫ Φ(merge x z) ψ_(-a)(Σ x_k α_k) dx`. `G` is integrable (Fubini on the
product, dominated by `Φ`) and continuous (`continuous_of_dominated` with the decay bound).
By Fubini, `fourier (-a) G y = fourier (-a) Φ (merge α y)` (`hslice`). This is integrable because
it is a Schwartz function composed with `merge α`. Fourier inversion (step 1, at `-a`) then gives
`G β = ∫ fourier (-a) G y ψ_a(Σ y_k β_k) dy`.

**4. Gluing (section Block).** `blockEquiv σ` glues `(v, X)` along an equivalence
`σ : κ₁ ⊕ κ₂ ≃ ρ` (`sumPiEquivProdPi` followed by `piCongrLeft`). It is measure-preserving for the
self-dual product measures (`measurePreserving_blockEquiv`, `integral_blockEquiv`), and
`sum_blockEquiv` splits a linear form along it.

**5. Matrices (sections Matrices, Jacquet).** `flatM` views a matrix as a function on index
pairs. `mul_weylLong_apply` and `weylLong_mul_apply` show that `w` reverses columns, resp. rows.
On positions `(i, j)` of an `(n+1) × (n+2)` matrix, `lowerPos n (i, j)` means `i + j < n + 1`.

- `sigmaL n : Upper n ⊕ Fin (n+1) ≃ {q // lowerPos n q}` sends `(i, j)` to `(i, n+1-j)` and
  `i` to `(i, 0)`. `flatM_blockA_mul_weylLong` shows
  `flatM (A(v,X) w_(n+2)) = merge (lowerPos n) (blockEquiv (sigmaL n) (v, X)) (betaR n)`, where
  `betaR` is the indicator of `i + j = n + 1` on the complementary block.
- `sigmaR n : Upper n ⊕ Fin (n+1) ≃ {q // ¬ lowerPos n q}` sends `(i, j)` to `(n-i, j)` and `i`
  to `(n-i, n+1)`. `flatM_weylLong_mul_blockA` shows
  `flatM (w_(n+1) A(v,X)) = merge (lowerPos n) (alphaL n) (blockEquiv (sigmaR n) (v, X))`, where
  `alphaL` is the indicator of `i + j = n` on the block `lowerPos`.
- `superdiagSum_eq_left` and `superdiagSum_eq_right` (via `sum_upper_superdiag`, `sum_fin_last`)
  show `S(v,X) = Σ_q blockEquiv (sigmaL n) (v,X) q · alphaL n q =
  Σ_q blockEquiv (sigmaR n) (v,X) q · betaR n q`.
- `flat Φ` is `Φ` composed with currying (`curryCLE`), a Schwartz function on
  `ℂ^((n+1) × (n+2))`. `rectFourier_eq_fourier` identifies `rectFourier a Φ Y` with
  `fourier a (flat Φ) (flatM Y)` (via `measurePreserving_uncurry`).

`integral_blockA_mul_weylLong_eq` rewrites both integrands with these identities, transports
both integrals along `blockEquiv (sigmaL n)` and `blockEquiv (sigmaR n)`, and concludes with
`integral_merge_left_eq a (flat Φ) (alphaL n) (betaR n)`.

The remaining declarations are auxiliary: `pi_smul_const`, `curryLinearEquiv`, `realify_apply`,
`inner_realify`, `selfDual_measure(_neg)`, `piMeasure_neg`, `pairing_apply`, `pairing_symm`,
`psi_apply`, `norm_psi`, `continuous_psi`, `twist_apply`, `twistPi`, `twistPi_apply`,
`measurePreserving_twist`, `pairing_eq_inner`, the `merge_apply*`, `continuous_merge`,
`norm_le_norm_merge*`, `sum_merge_mul_merge` lemmas, `blockEquiv_apply`, `flatM_apply`,
`curry_flatM`, `unip_apply`, `blockA_of_val(_last)` and `flat_apply`.
