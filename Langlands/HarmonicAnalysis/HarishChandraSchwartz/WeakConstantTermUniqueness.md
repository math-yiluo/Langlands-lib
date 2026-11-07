# The limit `lim_{a →_P ∞}` and uniqueness of the weak constant term (Waldspurger, III.5 and Lemma III.5.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib (multivariate polynomials,
polynomial roots and Taylor shifts, complex numbers, dual spaces, filters at infinity).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted displays below carry no overline in the printed text (checked on the
rendered PDF pages 35 and 36).

- III.5, printed p. 269 (PDF p. 35): "Soit `P = MU` un sous-groupe parabolique semi-standard de
  `G`. Pour une fonction `f : A_M → ℂ`, on écrit `lim_{a →_P ∞} f(a) = 0` si pour tous
  `ε, η > 0`, il existe `R > 0` tel que, pour tout `a ∈ A_M` vérifiant les conditions
  (i) `⟨α, H_M(a)⟩ > R` pour tout `α ∈ Σ(P)`;
  (ii) `⟨α, H_M(a)⟩ > η ⟨β, H_M(a)⟩` pour tous `α, β ∈ Σ(P)`,
  on ait `|f(a)| < ε`."
- Lemma III.5.1, printed p. 269: "Soit `f ∈ A^w(G)`. Il existe un unique élément
  `f^w_P ∈ A^w(M)` tel que pour tout `m ∈ M`,
  `lim_{a →_P ∞} [δ_P(ma)^{-1/2} f(ma) − f^w_P(ma)] = 0`."
- Its proof, printed p. 270 (PDF p. 36), display (1): "Il existe un ensemble fini
  `E ⊂ Hom(A_M, ℂ^*)` et pour tout `χ ∈ E`, un polynôme `Q_χ` sur `a_M` de sorte que pour tout
  `a ∈ A_M`, `ϕ(a) = Σ_{χ ∈ E} Q_χ(H_M(a)) χ(a)`, [...]".
- The uniqueness part of that proof, printed p. 270: "Supposons que deux éléments `f^w_P` et
  `f'^w_P` de `A^w(M)` vérifient cette condition. Fixons `m ∈ M` et définissons une fonction
  `ϕ : A_M → ℂ` par `ϕ(a) = f^w_P(ma) − f'^w_P(ma)`. Il existe `E` et des polynômes `Q_χ` comme
  ci-dessus de sorte que (1) soit vérifiée et `Re(χ) = 0` pour tout `χ ∈ E`. La fonction `ϕ`
  vérifie `lim_{a →_P ∞} ϕ(a) = 0`. Il en est de même de toute fonction dans l'espace engendré
  par les translatés de `ϕ` par des élément de `A_M`. Or tout élément de `E` appartient à cet
  espace. Donc `lim_{a →_P ∞} χ(a) = 0` pour tout `χ ∈ E`. Cela contredit l'unitarité des
  éléments de `E`, sauf si `E = ∅`. Donc `E = ∅`, `ϕ = 0` et `f^w_P = f'^w_P`."
- I.1, printed p. 239 (PDF p. 5): for `χ ∈ Hom(A_G, ℂ^*)`, `Re(χ) = Re(|χ|)`, and
  `Im X(G) = {χ ∈ X(G); Re(χ) = 0}` "est le sous-ensemble des éléments unitaires de `X(G)`". So
  `Re(χ) = 0` means `|χ| = 1`, which is the unitarity hypothesis `‖χ_j(a)‖ = 1` below.
- I.2, printed p. 242 (PDF p. 8), for the form of the functions: "un polynôme `P_{χ,f}` sur `a_M`,
  à coefficients complexes".

## Contents

### The limit of III.5

`TendstoZeroAlongParabolic HM S f`, for a type `A`, a real vector space `E` (`[AddCommGroup E]`,
`[Module ℝ E]`), a map `HM : A → E`, a finite set `S : Finset (Module.Dual ℝ E)` and
`f : A → ℂ`, is the proposition

`∀ ε > 0, ∀ η > 0, ∃ R > 0, ∀ a, (∀ α ∈ S, R < α (HM a)) →
  (∀ α ∈ S, ∀ β ∈ S, η * β (HM a) < α (HM a)) → ‖f a‖ < ε`.

It is the definition of III.5 with `A` for `A_M`, `HM` for `H_M`, `E` for `a_M` and `S` for
`Σ(P)`; the pairing `⟨α, H_M(a)⟩` is the evaluation `α (HM a)`. No structure on `A` and no
property of `HM` is required by the definition.

`TendstoZeroAlongParabolic.sub`: if `f` and `g` satisfy it, so does `a ↦ f a - g a` (derived; the
source uses it implicitly).

### Restriction to rays

With `[CommGroup A]`:

- `apply_mul_pow_of_map_mul`: if `HM (a * b) = HM a + HM b` for all `a, b`, then
  `HM (b * a₀ ^ k) = HM b + (k : ℝ) • HM a₀` for all `b, a₀ ∈ A` and `k : ℕ`.
- `eventually_lt_add_natCast_mul`: for real `c, R` and `d > 0`, eventually in `k : ℕ`,
  `R < c + k * d`.
- `TendstoZeroAlongParabolic.tendsto_mul_pow`: if `HM` is additive (hypothesis `hHM`),
  `TendstoZeroAlongParabolic HM S f`, and `a₀ ∈ A` satisfies `0 < α (HM a₀)` for every `α ∈ S`
  (hypothesis `ha₀`), then for every `b ∈ A` the sequence `k ↦ f (b * a₀ ^ k)` tends to `0` as
  `k → ∞`.

These three are derived results, not statements of the paper.

### Exponential polynomials

`exponentialPolynomial HM ℓ χ Q : A → ℂ`, for `ℓ : ι → Module.Dual ℝ E`, a finite type `κ`,
characters `χ : κ → A →* ℂˣ` and polynomials `Q : κ → MvPolynomial ι ℂ`, is

`a ↦ ∑ j, χ j a * Q j (ℓ i (HM a))_{i ∈ ι}`,

the polynomial `Q j` being evaluated at the real coordinates `ℓ i (HM a)` viewed in `ℂ`. This is
the form `Σ_{χ ∈ E} Q_χ(H_M(a)) χ(a)` of display (1): a complex polynomial on `a_M` is a
polynomial in the coordinates of a basis `ℓ` of the dual of `a_M`. The Lean definition allows any
family `ℓ` of linear forms and any indexed family of characters, possibly with repetitions; the
source's `E` is a finite set of characters.

`exists_eval_add_natCast_smul`: for `ℓ`, `x, v ∈ E` and `p : MvPolynomial ι ℂ` there is a
one-variable polynomial `P : ℂ[X]` with
`p (ℓ i (x + (k : ℝ) • v))_{i ∈ ι} = P (k)` for every `k : ℕ` (derived).

### Sequences on `ℕ`

For a normed field `𝕜` of characteristic zero and a finite type `ι`:

- `eq_zero_of_tendsto_sum_pow_mul_eval`: if `ν : ι → 𝕜` is injective (`hν`), `1 ≤ ‖ν i‖` for every
  `i` (`hν1`), `Q : ι → 𝕜[X]`, and `k ↦ ∑ i, ν i ^ k * Q i (k)` tends to `0`, then `Q i = 0` for
  every `i`.
- `eq_zero_of_tendsto_sum_pow_mul_eval_of_le`: the same with an additional natural number `N` and
  hypothesis `∑ i, (if Q i = 0 then 0 else natDegree (Q i) + 1) ≤ N` (the induction behind the
  previous statement).
- `sum_pow_mul_eval_eq_zero_of_tendsto`: if `1 ≤ ‖ν i‖` for every `i` (no injectivity) and
  `k ↦ ∑ i, ν i ^ k * Q i (k)` tends to `0`, then `∑ i, ν i ^ k * Q i (k) = 0` for every `k : ℕ`.

These are derived results, not statements of the paper.

### Uniqueness

`exponentialPolynomial_eq_zero_of_tendstoZeroAlongParabolic` (the uniqueness step of the proof of
Lemma III.5.1 for one function `ϕ`). Hypotheses: `[CommGroup A]`; `hHM : ∀ a b,
HM (a * b) = HM a + HM b`; `S : Finset (Module.Dual ℝ E)`; `a₀ : A` with
`ha₀ : ∀ α ∈ S, 0 < α (HM a₀)`; `ℓ : ι → Module.Dual ℝ E`; characters `χ : κ → A →* ℂˣ` with
`hχ : ∀ j a, ‖(χ j a : ℂ)‖ = 1` (`Re(χ) = 0`); polynomials `Q : κ → MvPolynomial ι ℂ`; and
`h : TendstoZeroAlongParabolic HM S (exponentialPolynomial HM ℓ χ Q)`. Conclusion:
`exponentialPolynomial HM ℓ χ Q b = 0` for every `b : A`.

`eq_of_tendstoZeroAlongParabolic` (the uniqueness of `f^w_P` in Lemma III.5.1). Hypotheses: a
monoid `M`, a monoid homomorphism `j : A →* M` (the inclusion `A_M ⊂ M`, the product `ma` being
`m * j a`), `[CommGroup A]`, `hHM`, `S`, `a₀` with `ha₀` and `ℓ` as above, functions
`F f₁ f₂ : M → ℂ`, and

- `h₁ : ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f₁ (m * j a))`;
- `h₂ : ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f₂ (m * j a))`;
- `hexp`: for every `m ∈ M` there are `n : ℕ`, characters `χ : Fin n → A →* ℂˣ` with
  `‖(χ i a : ℂ)‖ = 1` for all `i, a`, and `Q : Fin n → MvPolynomial ι ℂ` with
  `f₁ (m * j a) - f₂ (m * j a) = exponentialPolynomial HM ℓ χ Q a` for every `a`.

Conclusion: `f₁ = f₂`.

In the source `F(g) = δ_P(g)^{-1/2} f(g)` for `f ∈ A^w(G)`, and `f₁ = f^w_P`, `f₂ = f'^w_P` are
elements of `A^w(M)`. The hypothesis `hexp` is the source's sentence "Il existe `E` et des
polynômes `Q_χ` comme ci-dessus de sorte que (1) soit vérifiée et `Re(χ) = 0` pour tout
`χ ∈ E`", which the source derives from the structure of `A^w(M)` (I.2); that derivation, the
spaces `A^w(G)`, `A^w(M)`, the modulus `δ_P` and the existence half of Lemma III.5.1 are not in
this module. The additivity of `H_M` and the existence of `a₀` (an element of `A_M` in the open
positive chamber of `P`) are properties of Waldspurger's `H_M` and `A_M` that enter here as
hypotheses.

## Proof

`eq_zero_of_tendsto_sum_pow_mul_eval_of_le` is proved by induction on `N`, following the proof of
`Langlands.BruhatTits.RationalPoints.CentralNormKernel.eq_zero_of_sum_pow_mul_eval_eq_zero_of_le`
(Worker 1045) with the vanishing hypothesis replaced by convergence to `0`. If some `Q j ≠ 0`, the
difference operator `a ↦ (k ↦ a (k + 1) - ν j * a k)` replaces `Q i` by
`ν i * Q i (X + 1) - ν j * Q i`; the new sequence again tends to `0`, and the total size
decreases (strictly at `j`), so the new polynomials all vanish by induction. Comparing leading
coefficients and using the injectivity of `ν` gives `Q i = 0` for `i ≠ j`, and `ν j ≠ 0` (from
`‖ν j‖ ≥ 1`) gives `Q j (X + 1) = Q j`, so `Q j` is constant on `ℕ`. The sequence is then
`ν j ^ k * Q j (0)`, of norm at least `‖Q j (0)‖`; its limit `0` forces `Q j (0) = 0`, so `Q j`
has infinitely many roots and vanishes, a contradiction. `sum_pow_mul_eval_eq_zero_of_tendsto`
groups the indices by the value of `ν` and applies the injective statement to the summed
polynomials.

`TendstoZeroAlongParabolic.tendsto_mul_pow` chooses `η₀ > 0` with
`η₀ * β (HM a₀) < α (HM a₀)` for all `α, β ∈ S` (continuity at `η = 0`, `S` finite). Along
`k ↦ b * a₀ ^ k` one has `α (HM (b * a₀ ^ k)) = α (HM b) + k * α (HM a₀)`, so conditions (i) for
any `R` and (ii) for `η₀` hold for all large `k`, and the definition gives `‖f (b * a₀ ^ k)‖ < ε`.

`exponentialPolynomial_eq_zero_of_tendstoZeroAlongParabolic`: along the ray `k ↦ b * a₀ ^ k`,
`exists_eval_add_natCast_smul` turns `ϕ (b * a₀ ^ k)` into `∑ j, χ j a₀ ^ k * (χ j b * P j) (k)`
with one-variable polynomials `P j`. This sequence tends to `0` by `tendsto_mul_pow`, and
`‖χ j a₀‖ = 1`, so `sum_pow_mul_eval_eq_zero_of_tendsto` makes it vanish identically; at `k = 0`
it is `ϕ (b)`.

This route differs from the source's: the source passes to the space spanned by the translates of
`ϕ` under `A_M`, which contains every `χ ∈ E`, and concludes from `lim_{a →_P ∞} χ(a) = 0` and
`|χ| = 1`. The Lean proof restricts `ϕ` to rays instead and uses only `‖χ_j‖ = 1` and the
convergence along one ray through each point.

`eq_of_tendstoZeroAlongParabolic`: for fixed `m`, the difference of `h₂ m` and `h₁ m`
(`TendstoZeroAlongParabolic.sub`) is the limit statement for `a ↦ f₁ (m * j a) - f₂ (m * j a)`,
which is an exponential polynomial with unitary characters by `hexp`; the previous theorem at
`b = 1` gives `f₁ m = f₂ m`.
