# Existence of the weak constant term (Waldspurger, Lemma III.5.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermExistence`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness` (for
`TendstoZeroAlongParabolic`, `exponentialPolynomial` and `eq_of_tendstoZeroAlongParabolic`) and
`Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics` (polynomials against exponentials).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Overlines in the quotes below were checked on the rendered PDF pages 5, 6, 15, 31 and 36.

- Lemma III.5.1, printed p. 269 (PDF p. 35): "Soit `f ∈ A^w(G)`. Il existe un unique élément
  `f^w_P ∈ A^w(M)` tel que pour tout `m ∈ M`,
  `lim_{a →_P ∞} [δ_P(ma)^{-1/2} f(ma) − f^w_P(ma)] = 0`." The limit `lim_{a →_P ∞}` is the one
  of III.5 (conditions (i) and (ii)), formalized as `TendstoZeroAlongParabolic` in
  `WeakConstantTermUniqueness`.
- The existence part of its proof, printed p. 270 (PDF p. 36): "Fixons `m ∈ M`, définissons une
  fonction `ϕ : A_M → ℂ` par `ϕ(a) = f_P(ma) − f^w_P(ma)`. [...] Il existe un ensemble fini
  `E ⊂ Hom(A_M, ℂ^*)` et pour tout `χ ∈ E`, un polynôme `Q_χ` sur `a_M` de sorte que
  pour tout `a ∈ A_M`, `ϕ(a) = Σ_{χ ∈ E} Q_χ(H_M(a)) χ(a)`,
  pour tout `χ ∈ E`, `Re(χ) ∈ +ā_P^{G*}` et `Re(χ) ≠ 0`. (1)
  Ces conditions assurent que `lim_{a →_P ∞} ϕ(a) = 0`. Mais alors on a aussi
  `lim_{a →_P ∞} [δ_P(ma)^{-1/2} f(ma) − f^w_P(ma)] = 0`. Donc `f^w_P` vérifie la condition
  requise." In display (1) the `a` of `+ā_P^{G*}` carries an overline; `f_P` and `f^w_P` carry
  none.
- I.1, printed p. 239 (PDF p. 5): "On note `+a_P^{G*}`, resp. `+ā_P^{G*}`, l'ensemble des
  `χ ∈ a_M^*` de la forme `χ = Σ_{α ∈ Δ(P)} x_α α` avec des coefficients `x_α > 0`, resp.
  `x_α ⩾ 0`." On the same page: the surjection `a_{G,ℂ}^* → X(G)` "qui à `χ ⊗ s` associe le
  caractère `g ↦ |χ(g)|_F^s`", `Re(χ)` is the real part of a preimage, and for
  `χ ∈ Hom(A_G, ℂ^*)`, `Re(χ) = Re(|χ|)`.
- I.1, printed p. 240 (PDF p. 6): "On définit un homomorphisme `H_G : G → a_G` par la relation
  `q^{-⟨χ, H_G(g)⟩} = |χ|_F(g)` pour tout `χ ∈ Rat(G)`", and these definitions apply to every
  Levi subgroup `M` in place of `G`.
- Proposition I.6.2, printed p. 249 (PDF p. 15), for the constant term `f_P`: "pour tout
  `m ∈ M`, il existe `ε > 0` tel que pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε` pour tout
  `α ∈ Σ(P)`, on ait l'égalité `δ_P(ma)^{-1/2} f(ma) = f_P(ma)`."
- III.2, printed p. 265 (PDF p. 31): `C^w_lisse(G)` is the space of `f ∈ C_lisse(G)` with
  `|f(g)| ⩽ cΞ(g)(1 + σ(g))^r` for some `c > 0`, `r ∈ ℝ`, and
  "`A^w(G) = A(G) ∩ C^w_lisse(G)`".

### How `IsDecayingAlongParabolic` encodes `Re(χ) ∈ +ā_P^{G*}`, `Re(χ) ≠ 0`

By the I.1 definitions quoted above, the character of `A_M` attached to `λ ∈ a_{M,ℂ}^*` is
`a ↦ q^{-⟨λ, H_M(a)⟩}`, so `|χ(a)| = q^{-⟨Re(χ), H_M(a)⟩}` for `χ ∈ Hom(A_M, ℂ^*)`. If
`Re(χ) = Σ_{α ∈ Δ(P)} y_α α` with all `y_α ⩾ 0` and `Re(χ) ≠ 0`, then some `y_α > 0`, and
`|χ(a)| = exp(-Σ_α (log q) y_α ⟨α, H_M(a)⟩)`. Since `Δ(P) ⊂ Σ(P)`, this is
`IsDecayingAlongParabolic H_M Σ(P) χ` with `x_α = (log q) y_α` on `Δ(P)` and `x_α = 0` on
`Σ(P) ∖ Δ(P)`. This unwinding is derived here and is not formalized; the Lean definition uses an
inequality and any finite set `S` of linear forms in place of `Σ(P)`.

### A gap in the source's existence argument

The sentence "Ces conditions assurent que `lim_{a →_P ∞} ϕ(a) = 0`" is not correct for
conditions (1) as stated. The roots `α ∈ Σ(P)` vanish on `a_G` (they are roots of `A_M` in
`Lie(G)`, and `A_G` is central in `G`), so conditions (i) and (ii) of III.5 say nothing about the
`a_G`-component of `H_M(a)`, while (1) allows `Q_χ` to be any polynomial on `a_M`.

Example (in prose; not formalized): `G = GL_2(F)`, `P = B` the upper triangular Borel subgroup,
`M = T` the diagonal torus, `St` the Steinberg representation and `c(g) = ⟨St(g)v, v̌⟩` a
coefficient with nonzero constant term along `B`. The function `f(g) = val_F(det g) c(g)` is a
coefficient of the admissible representation `St ⊗ U`, where `U` is the two-dimensional
representation `g ↦ [[1, val_F(det g)], [0, 1]]`, and `|f(g)| ⩽ C(1 + σ(g))|c(g)|` for a constant `C`, so `f ∈ A^w(G)`.
Its constant term is `f_B(t) = val_F(det t) c_B(t)` with `c_B` a nonzero multiple of
`δ_B^{1/2}`, which is not unitary, so the weak Jacquet module of `St ⊗ U` along `B` is zero and
the source's `f^w_B` is `0`. For `t` in the chamber with `⟨α, H_T(t)⟩` fixed and `z` central,
`f_B(zt) = (2 val_F(z) + val_F(det t)) c_B(t)` is unbounded in `z`, while conditions (i) and (ii)
do not depend on `z`; so `lim_{a →_B ∞} [δ_B(a)^{-1/2} f(a) − g(a)] = 0` fails for `g = 0`. It fails for every
`g ∈ A^w(T)` as well: such `g` is an exponential polynomial with unitary characters, and it
cannot compensate the term `2 val_F(z) c_B(t)`, whose coefficient `c_B(t)` is a multiple of the
non-unitary character `δ_B^{1/2}(t)` (sketch only). The existence statement of Lemma III.5.1 thus fails for this `f`.

The argument is correct when every `Q_χ` factors through the projection `a_M → a_M^G`, i.e. is a
polynomial in linear forms in the span of `Σ(P)`; for instance, when `A_G` acts on the representation
generated by `f` through a character, each `Q_χ` is invariant under translation by `a_G`, hence a
polynomial in forms vanishing on `a_G`, and these lie in the span of `Σ(P)` by the standard fact
that `Δ(P)` is a basis of the annihilator of `a_G` in `a_M^*` (not stated in this form in the
paper; this remark is not formalized). The Lean statements below carry this as the
explicit hypothesis `hℓ`, and `not_tendstoZeroAlongParabolic_fst_mul_expNegSnd` formalizes an
abstract version of the failure.

## Contents

Throughout, `E` is a real vector space (`[AddCommGroup E]`, `[Module ℝ E]`, the source's `a_M`),
`HM : A → E` (the source's `H_M`), and `S : Finset (Module.Dual ℝ E)` (the source's `Σ(P)`).

### Bounds (derived; not statements of the paper)

- `exists_norm_eval_le (p : MvPolynomial ι ℂ)`: there are a finite set `s` of variables, `C ≥ 0`
  and `d : ℕ` such that `‖MvPolynomial.eval x p‖ ≤ C * M ^ d` for all `x : ι → ℂ` and `M ≥ 1`
  with `‖x i‖ ≤ M` for every `i ∈ s`.
- `exists_abs_apply_le_of_mem_span`: if `ℓ ∈ Submodule.span ℝ S` (hypothesis `hℓ`), there is
  `C ≥ 0` with `|ℓ H| ≤ C * T` for all real `T` and `H : E` such that `|α H| ≤ T` for every
  `α ∈ S`.
- `eventually_mul_pow_mul_exp_neg_lt`: for `c > 0` (`hc`), `K ≥ 0` (`hK`), real `D`, `d : ℕ` and
  `ε > 0` (`hε`), eventually as `t → ∞`, `D * (1 + K * t) ^ d * exp (-(c * t)) < ε`.

### Limits along `P`

- `TendstoZeroAlongParabolic.congr_of_forall` (derived): for any type `A`, `HM`, `S`,
  `f g : A → ℂ`, `hg : TendstoZeroAlongParabolic HM S g`, a real `R₀` and
  `hfg : ∀ a, (∀ α ∈ S, R₀ < α (HM a)) → f a = g a`, also `TendstoZeroAlongParabolic HM S f`.

From here on `A` is a commutative group (`[CommGroup A]`, the source's `A_M`).

- `IsDecayingAlongParabolic HM S χ`, for `χ : A →* ℂˣ`, is the proposition: there is
  `x : Module.Dual ℝ E → ℝ` with `0 ≤ x α` for all `α ∈ S`, `0 < x α` for some `α ∈ S`, and
  `‖(χ a : ℂ)‖ ≤ Real.exp (-∑ α ∈ S, x α * α (HM a))` for every `a : A`. It is the second line of
  display (1), `Re(χ) ∈ +ā_P^{G*}` and `Re(χ) ≠ 0`, as explained above.
- `tendstoZeroAlongParabolic_exponentialPolynomial`: hypotheses `HM : A → E` (no additivity
  needed), `S`, linear forms `ℓ : ι → Module.Dual ℝ E` with
  `hℓ : ∀ i, ℓ i ∈ Submodule.span ℝ S`, a finite type `κ`, characters `χ : κ → A →* ℂˣ` with
  `hχ : ∀ j, IsDecayingAlongParabolic HM S (χ j)`, and polynomials
  `Q : κ → MvPolynomial ι ℂ`. Conclusion:
  `TendstoZeroAlongParabolic HM S (exponentialPolynomial HM ℓ χ Q)`, where
  `exponentialPolynomial HM ℓ χ Q a = ∑ j, χ j a * Q j (ℓ i (HM a))_{i ∈ ι}` is the form of the
  first line of display (1). This is the sentence "Ces conditions assurent que
  `lim_{a →_P ∞} ϕ(a) = 0`" with the added hypothesis `hℓ`.
- `tendstoZeroAlongParabolic_sub_of_eventually_eq` (the existence argument). Hypotheses: a monoid
  `M`, a monoid homomorphism `j : A →* M` (the product `ma` is `m * j a`), `HM`, `S`, `ℓ` with
  `hℓ` as above, functions `F fP fw : M → ℂ`, and
  - `hasym : ∀ m, ∃ R : ℝ, ∀ a, (∀ α ∈ S, R < α (HM a)) → F (m * j a) = fP (m * j a)`;
  - `hdec`: for every `m` there are `n : ℕ`, `χ : Fin n → A →* ℂˣ` with
    `IsDecayingAlongParabolic HM S (χ i)` for every `i`, and `Q : Fin n → MvPolynomial ι ℂ` with
    `fP (m * j a) - fw (m * j a) = exponentialPolynomial HM ℓ χ Q a` for every `a`;
  - a point `m : M`.

  Conclusion: `TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - fw (m * j a))`.

  In the source `F(g) = δ_P(g)^{-1/2} f(g)`, `fP = f_P`, `fw = f^w_P`. `hasym` is
  Proposition I.6.2: `|α(a)|_F = q^{-⟨α, H_M(a)⟩}` turns `|α(a)|_F < ε` into
  `⟨α, H_M(a)⟩ > -log_q ε` (derived, not formalized). `hdec` is display (1) with the span
  hypothesis on the coordinates; its derivation from the Jacquet module structure (the identity
  `ϕ(a) = ⟨π^+_P(ma) j^+_P(v), ǰ^+_P̄(v̌)⟩_P` and the exponents of `π^+_P`) is not in this module.
- `existsUnique_tendstoZeroAlongParabolic_sub` (Lemma III.5.1 with the existence argument above
  and the uniqueness of `WeakConstantTermUniqueness`). Hypotheses: `M`, `j`, `HM` with
  `hHM : ∀ a b, HM (a * b) = HM a + HM b`, `S`, `a₀ : A` with `ha₀ : ∀ α ∈ S, 0 < α (HM a₀)`,
  `ℓ` with `hℓ`, a further family `ℓ' : ι' → Module.Dual ℝ E` (no span condition), `F fP fw`,
  a set `C : Set (M → ℂ)` (the source's `A^w(M)`) with `hfw : fw ∈ C`, `hasym` and `hdec` as
  above, and
  - `hC`: for all `g₁ g₂ ∈ C` and every `m` there are `n`, `χ : Fin n → A →* ℂˣ` with
    `‖(χ i a : ℂ)‖ = 1` for all `i, a`, and `Q : Fin n → MvPolynomial ι' ℂ` with
    `g₁ (m * j a) - g₂ (m * j a) = exponentialPolynomial HM ℓ' χ Q a` for every `a`.

  Conclusion: `∃! g, g ∈ C ∧ ∀ m, TendstoZeroAlongParabolic HM S
  (fun a => F (m * j a) - g (m * j a))`.

  `hC` is the source's "Il existe `E` et des polynômes `Q_χ` comme ci-dessus de sorte que (1)
  soit vérifiée et `Re(χ) = 0` pour tout `χ ∈ E`" for elements of `A^w(M)`; it is not derived
  here. The spaces `A^w(G)`, `A^w(M)`, the modulus `δ_P` and the Jacquet-module definition of
  `f^w_P` do not occur in this module.

### The span hypothesis cannot be dropped

- `expNegSnd : Multiplicative (ℝ × ℝ) →* ℂˣ` is the character `a ↦ e^{-a₂}`.
- `not_tendstoZeroAlongParabolic_fst_mul_expNegSnd`: for `A = Multiplicative (ℝ × ℝ)`,
  `HM = Multiplicative.toAdd` and `S = {LinearMap.snd ℝ ℝ ℝ}`: (1) `expNegSnd` satisfies
  `IsDecayingAlongParabolic`; (2) `LinearMap.fst ℝ ℝ ℝ` is not in the span of `S`; (3) the
  exponential polynomial `a ↦ e^{-a₂} a₁` (one character `expNegSnd`, `ℓ = fst`, `Q = X`) does
  not satisfy `TendstoZeroAlongParabolic HM S`. This is an abstract analogue of the `GL_2`
  example above (first coordinate for the `a_G`-direction); it does not formalize that example.

## Proof

`exists_norm_eval_le` is by `MvPolynomial.induction_on`: constants give `C = ‖c‖`, `d = 0`;
sums take the union of variable sets, `C₁ + C₂` and `max d₁ d₂` (using `M ≥ 1`); multiplication
by `X i` adds `i` and raises `d` by one. `exists_abs_apply_le_of_mem_span` is by
`Submodule.span_induction` with constants `1`, `0`, `C₁ + C₂` and `|r| C`.
`eventually_mul_pow_mul_exp_neg_lt` uses `isLittleO_pow_exp_pos_mul_atTop` and, for `t ≥ 1`,
`(1 + K t)^d ≤ (1 + K)^d t^d`.

`tendstoZeroAlongParabolic_exponentialPolynomial`: given `ε, η > 0`, if `S` is empty there are no
decaying characters (`IsDecayingAlongParabolic` needs some `α ∈ S`), so `κ` is empty and the
function is `0`. Otherwise fix `α₀ ∈ S` and put `t = ⟨α₀, H_M(a)⟩`. Condition (ii) gives
`|⟨β, H_M(a)⟩| ≤ t/η` for every `β ∈ S` (with (i) for positivity), hence `|ℓ_i(H_M(a))| ≤ C_i t/η`
and `|Q_j(...)| ≤ D_j (1 + K_j t)^{d_j}`. For `χ_j` with `x_j(α_j) > 0`, condition (ii) gives
`⟨α_j, H_M(a)⟩ > η t`, so `|χ_j(a)| ≤ exp(-x_j(α_j) η t)`. By
`eventually_mul_pow_mul_exp_neg_lt` there is `T` beyond which every term is below
`ε / (card κ + 1)`; `R = max T 1` makes condition (i) force `t > T`, and the sum of the terms is
below `ε`.

`tendstoZeroAlongParabolic_sub_of_eventually_eq` applies the previous theorem to the exponential
polynomial of `hdec m` and transfers the limit by `congr_of_forall` with the threshold `R` of
`hasym m`. `existsUnique_tendstoZeroAlongParabolic_sub` takes `g = fw` for existence and, for
uniqueness, applies `eq_of_tendstoZeroAlongParabolic` of `WeakConstantTermUniqueness` to `g`,
`fw` and the exponential polynomials of `hC g fw`.

For the counterexample, `IsDecayingAlongParabolic` holds with `x = 1` (equality). The first
coordinate `fst` is not a multiple of `snd` since `snd (1, 0) = 0 ≠ 1 = fst (1, 0)`. For any
`R > 0` from the definition with `ε = η = 1/2`, the point `a = (e^{R+1}, R + 1)` satisfies (i)
and (ii) (the only form is `snd`, and `(1/2)(R + 1) < R + 1`), but
`ϕ(a) = e^{R+1} e^{-(R+1)} = 1`, which is not below `1/2`.
