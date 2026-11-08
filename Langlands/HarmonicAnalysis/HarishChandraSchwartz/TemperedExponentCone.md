# Exponents of tempered representations lie in the closed positive cone (Waldspurger, Proposition III.2.2, (i) ⇒ (ii))

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedExponentCone`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.Representation.Jacquet.StablePairingAsymptotics` (for
`IsStablePairing.exists_pow_asymptotics`, the asymptotic formula along powers),
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability` (for
`le_one_of_pow_le` and `le_add_nsmul_of_subadditive`; `HasTemperedCoefficients` of
`SchwartzAction` is available through these imports) and `Mathlib.LinearAlgebra.Dual.Lemmas` (for
`LinearMap.dualMap_injective_iff`).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Overlines and calligraphic letters in the quotes below were checked on the
rendered PDF pages 5, 6, 9, 17, 31 and 32.

- Proposition III.2.2, printed p. 265 (PDF p. 31): "Soit `(π, V)` une représentation admissible
  de `G`. Les conditions suivantes sont équivalentes: (i) `π` est tempérée; (ii) pour tout
  sous-groupe parabolique semi-standard `P` de `G` et tout `χ ∈ 𝓔xp(π_P)`,
  `Re(χ) ∈ +ā_P^{G*}`; (iii) [...]". The `a` of `+ā_P^{G*}` carries an overline and `𝓔xp` is
  calligraphic. This module treats (i) ⇒ (ii) only.
- The proof of (i) ⇒ (ii), printed p. 266 (PDF p. 32): "Supposons `π` tempérée et soient
  `P = MU` et `χ` comme en (ii). D'après I.2 et le Théorème I.4.1, il existe `v ∈ V`,
  `v̌ ∈ V̌` et `ε > 0` tels que `χ(a) = δ_P(a)^{-1/2}⟨π(a)v, v̌⟩` pour tout `a ∈ A_M` tel que
  `|α(a)|_F < ε` pour tout `α ∈ Δ(P)`. Comme `π` est tempérée, le Lemme II.1.1 implique
  l'existence de `c > 0` et `d ∈ ℕ` tels que `|χ(a)| ⩽ c(1 + σ(a))^d` pour tout `a` comme
  ci-dessus. Ecrivons `Re(χ) = z + Σ_{α ∈ Δ(P)} x_α α`, avec `z ∈ a_G^*` et `x_α ∈ ℝ` pour
  tout `α`. Notons `{ω_α; α ∈ Δ(P)}` la base de `a_M^G (= a_M ∩ a^G)` duale de `Δ(P)`. Il
  existe un réseau `L ⊂ a_G` et un entier `N` tel que le réseau
  `L ⊕ (⊕_{α ∈ Δ(P)} ℤNω_α)` soit inclus dans `H_M(A_M)`. La majoration ci-dessus entraîne
  qu'il existe `c' > 0` et `N' ∈ ℕ` tels que pour tout `ℓ ∈ L` et tout
  `(y_α)_{α ∈ Δ(P)} ∈ ℕ^{Δ(P)}` vérifiant `y_α > N'` pour tout `α`, on ait
  `q^{-⟨z,ℓ⟩ - Σ_α N x_α y_α} ⩽ c'(1 + |ℓ| + Σ_α y_α)^d`. Il en résulte que `z = 0` et
  `x_α ⩾ 0` pour tout `α`, i.e. `Re(χ) ∈ +ā_P^{G*}`."
- I.1, printed p. 239 (PDF p. 5): "On note `+a_P^{G*}`, resp. `+ā_P^{G*}`, l'ensemble des
  `χ ∈ a_M^*` de la forme `χ = Σ_{α ∈ Δ(P)} x_α α` avec des coefficients `x_α > 0`, resp.
  `x_α ⩾ 0`." On the same page: `a_M = (Rat(A_M) ⊗_ℤ ℝ)^*`; `Σ(P)` and `Δ(P)` are the positive
  and the simple roots of `A_M` relative to `P`; `ā_0^+ = {H ∈ a_0; ∀α ∈ Δ_0, ⟨α, H⟩ ⩾ 0}`; the
  surjection `a_{G,ℂ}^* → X(G)` "qui à `χ ⊗ s` associe le caractère `g ↦ |χ(g)|_F^s`";
  `Re(χ)` is the real part of a preimage, and for `χ ∈ Hom(A_G, ℂ^*)`, "le caractère `|χ|` se
  prolonge de façon unique en un élément de `X(G)` à valeurs réelles `> 0`" and
  `Re(χ) = Re(|χ|)`.
- I.1, printed p. 240 (PDF p. 6): "On définit un homomorphisme `H_G : G → a_G` par la relation
  `q^{-⟨χ, H_G(g)⟩} = |χ|_F(g)` pour tout `χ ∈ Rat(G)`"; these definitions apply to every Levi
  subgroup `M` in place of `G`; `M̄_0^+ = H_{M_0}^{-1}(ā_0^+)` and `Ā_0^+ = M̄_0^+ ∩ A_0`.
- I.1, printed p. 242 (PDF p. 8): "`‖g‖ ⩾ 1`, `‖g_1g_2‖ ⩽ ‖g_1‖‖g_2‖`" and
  "`σ(g) = log‖g‖`".
- I.3, printed p. 243 (PDF p. 9): for `χ ∈ Hom(A_G, ℂ^*)`,
  "`V_χ = {v ∈ V; ∃d ∈ ℕ, ∀a ∈ A_G, (π(a) − χ(a))^d v = 0}`. On appelle exposant de `π` un
  caractère `χ` tel que `V_χ ≠ 0`. On note `𝓔xp(π)` l'ensemble de ces exposants." For
  `P = MU` semi-standard, `V_P` is the Jacquet module and "`π_P(m)j_P(v) =
  δ_P(m)^{-1/2}j_P(π(m)v)` pour tous `m ∈ M`, `v ∈ V`". So `𝓔xp(π_P)` consists of characters
  of `A_M`.
- Théorème I.4.1, printed p. 245 (PDF p. 11), quoted in `StablePairingAsymptotics.md`: a
  nondegenerate `M`-invariant pairing on `V_P × V̌_P̄` with
  `⟨π_P(a) j_P(v), ǰ_P̄(v̌)⟩_P = δ_P(a)^{-1/2} ⟨π(a)v, v̌⟩` when `|α(a)|_F < ε` for all
  `α ∈ Δ(P)`.
- Lemme II.1.1, printed p. 251 (PDF p. 17): "Il existe `C_1, C_2 > 0` et `d ∈ ℕ` tels que pour
  tout `m ∈ M̄_0^+`, on ait `C_1 δ_0(m)^{1/2} ⩽ Ξ(m) ⩽ C_2 δ_0(m)^{1/2}(1 + σ(m))^d`." Here
  `Ξ(g) = ∫_K δ_0(m_0(kg))^{1/2} dk` (same page), so `Ξ ⩾ 0`.
- III.2, printed p. 265 (PDF p. 31): `C^w_lisse(G)` is the space of `f ∈ C_lisse(G)` with
  `|f(g)| ⩽ cΞ(g)(1 + σ(g))^r` for some `c > 0`, `r ∈ ℝ`; "`A^w(G) = A(G) ∩ C^w_lisse(G)`";
  "On dit que `π` est tempérée si `A(π) ⊂ A^w(G)`."

The abstraction, the hypotheses and the proof route below are internal to this project.

## Relation to the source

Dictionary for `mem_closedPositiveCone_of_hasTemperedCoefficients`:

- `ρ` on `V` is the source's `π`; `hT : HasTemperedCoefficients Ξ σ ρ` (every coefficient
  `g ↦ ℓ(ρ(g)v)` is bounded by `c Ξ(g)(1 + σ(g))^r`) is the definition of tempered quoted from
  III.2. `Ξ ⩾ 0` and `σ ⩾ 0` subadditive hold for the source's `Ξ` and `σ = log‖·‖` by the
  quotes from II.1 and I.1.
- `Nbar` is the unipotent radical `U` of `P` (the Library's `Coinvariants ρ Nbar` is `V_P`),
  `M` is the Levi subgroup, `δ : M →* ℝ≥0ˣ` is `δ_P`, and the Library's
  `normalizedActionOfModulus ρ Nbar M hMNbar δ` is `π_P` (it sends the class of `v` under `m`
  to `δ(m)^{-1/2}` times the class of `ρ(m)v`).
- `A` is `A_M`, `j : A →* M` its inclusion, `E` is `a_M`, `HM` is `H_M` restricted to `A_M`,
  `S` is `Δ(P)`, and `closedPositiveCone S` is `+ā_P^{G*}`.
- `χ : A →* ℂˣ` and `y` encode `χ ∈ 𝓔xp(π_P)`: `y ≠ 0` is a vector of `(V_P)_χ`. The Lean
  hypothesis `hχ` lets the exponent `k` depend on `a`, which is weaker than the uniform `d` of
  I.3.
- `lam` is `Re(χ)` and `q` is the cardinality of the residue field `F_q` of `F` (I.1, printed
  p. 238).

Obligations for an actual group, derived here and not formalized:

- `hspan` (`H_M(A_M)` spans `a_M`) and `hS` (`Δ(P)` is linearly independent in `a_M^*`):
  standard; the proof quoted above uses that `Δ(P)` has a dual basis `{ω_α}` of `a_M^G` and a
  lattice `L ⊕ (⊕_α ℤNω_α) ⊂ H_M(A_M)`.
- `ha₀`: some `a₀ ∈ A_M` with `⟨α, H_M(a₀)⟩ > 0` for all `α ∈ Δ(P)`; it exists by the same
  lattice.
- `hD`: for every `a ∈ A_M` in the open chamber `{⟨α, H_M(a)⟩ > 0, α ∈ Δ(P)}`, Library
  `StablePairingData` with `Nbar = U` and contracting element `D.g = a⁻¹`, satisfying `Admits`.
  This is the input to Théorème I.4.1 in the abstract framework of
  `StablePairingAsymptotics`; the fields `D.N` and `D.M` are not constrained. Nothing here
  constructs these data for an actual reductive group (for the block parabolic subgroups of
  `GL_n` the Library constructs pairing data, see `StablePairingAsymptotics.md`).
- `hΞ` (`Ξ(a) ⩽ C δ_P(a)^{1/2}(1 + σ(a))^d` on the open chamber): from Lemme II.1.1 when `P` is
  standard, because then `A_M ⊂ A_0`, the open chamber lies in `Ā_0^+` (the roots in `Δ_0`
  restrict on `a_M` to `0` or to elements of `Δ(P)`), and `δ_0(a) = δ_P(a)` for `a ∈ A_M`
  (`a` is central in `M`). For semi-standard `P` one conjugates by a Weyl group element. The
  source invokes Lemme II.1.1 in the same place.
- `hlam` (`|χ(a)| = q^{-⟨Re(χ), H_M(a)⟩}`): from the I.1 definitions quoted above applied to
  `M`, the real positive character `|χ|` of `A_M` is `a ↦ q^{-⟨λ, H_M(a)⟩}` for a real
  preimage `λ`, and `Re(χ) = λ`.

## Contents

Throughout, `E` is a real vector space (`[AddCommGroup E]`, `[Module ℝ E]`) and
`S : Finset (Module.Dual ℝ E)`.

### The cone

- `closedPositiveCone S : Set (Module.Dual ℝ E)` (definition): the set of `lam` for which there
  is `x : Module.Dual ℝ E → ℝ` with `0 ≤ x α` for all `α ∈ S` and `lam = ∑ α ∈ S, x α • α`.
  With `S = Δ(P)` and `E = a_M` this is the source's `+ā_P^{G*}`.
- `abs_natCast_mul_sub_le` (derived): for a finite type `ι`, a basis `b : Module.Basis ι ℝ E`,
  `H : E`, `n : ℕ` and `φ : Module.Dual ℝ E`,
  `|n * φ H - φ (∑ i, ⌊n * b.repr H i⌋ • b i)| ≤ ∑ i, |φ (b i)|`.
- `nonneg_of_forall_mem_openChamber` (derived; density step): `[FiniteDimensional ℝ E]`, an
  additive subgroup `Λ` with `hΛ : Submodule.span ℝ Λ = ⊤`, `S`, `lam`,
  `h : ∀ x ∈ Λ, (∀ α ∈ S, 0 < α x) → 0 ≤ lam x`, and `H` with `hH : ∀ α ∈ S, 0 < α H`.
  Conclusion: `0 ≤ lam H`.
- `nonneg_of_forall_openChamber` (derived; closure step): `S`, `lam`, `H₀` with
  `hH₀ : ∀ α ∈ S, 0 < α H₀`, `h : ∀ H, (∀ α ∈ S, 0 < α H) → 0 ≤ lam H`, and `H` with
  `hH : ∀ α ∈ S, 0 ≤ α H`. Conclusion: `0 ≤ lam H`.
- `mem_closedPositiveCone_of_nonneg` (derived; dual cone of a linearly independent family):
  `[FiniteDimensional ℝ E]`, `hS : LinearIndependent ℝ ((↑) : S → Module.Dual ℝ E)`, `lam`,
  `h : ∀ H, (∀ α ∈ S, 0 ≤ α H) → 0 ≤ lam H`. Conclusion: `lam ∈ closedPositiveCone S`.

### From `|χ| ≤ 1` on the open chamber to the cone

- `mem_closedPositiveCone_of_norm_le_one`: `[FiniteDimensional ℝ E]`, a commutative group `A`,
  `HM : A → E` with `hHM : ∀ a b, HM (a * b) = HM a + HM b` and
  `hspan : Submodule.span ℝ (Set.range HM) = ⊤`, `S` with `hS` as above, `a₀` with
  `ha₀ : ∀ α ∈ S, 0 < α (HM a₀)`, `χ : A →* ℂˣ`, `q` with `hq : 1 < q`, `lam` with
  `hlam : ∀ a, ‖(χ a : ℂ)‖ = q ^ (-lam (HM a))`, and
  `h1 : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ‖(χ a : ℂ)‖ ≤ 1`.
  Conclusion: `lam ∈ closedPositiveCone S`. This replaces the last step of the quoted proof
  (from the bound on `|χ(a)|` to `z = 0`, `x_α ⩾ 0`).
- `norm_lt_one_of_norm_le_one` (derived): a commutative group `A`, `HM : A → E` with `hHM`,
  `S`, `a₀` with `ha₀ : ∀ α ∈ S, 0 < α (HM a₀)`, `χ : A →* ℂˣ` with
  `h1 : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ‖(χ a : ℂ)‖ ≤ 1` and
  `hne : ∃ b, ‖(χ b : ℂ)‖ ≠ 1`. Conclusion: `‖(χ a₀ : ℂ)‖ < 1`. With the dictionary below, a
  non-unitary exponent (`Re(χ) ≠ 0`) of a tempered representation is strictly smaller than `1`
  in modulus at every point of the open chamber; this is the inequality
  "`|(sp_χ ν')(a)| < 1`" that the proof of Lemma VI.2.1 (printed p. 298) derives from
  Proposition III.2.2. No `λ` and no spanning or independence hypothesis is needed.

### Growth lemmas (derived)

- `le_of_eventually_pow_mul_le`: reals `x, c, K, C`, `k : ℕ`, `hc : 0 < c`, `hK : 0 < K` and
  `h : ∀ᶠ r : ℕ in atTop, x ^ r * K ≤ C * c ^ r * (1 + r) ^ k`. Conclusion: `x ≤ c`.
- `one_add_rpow_le_of_subadditive`: for a group `G`, `σ : G → ℝ` with `hσ0 : ∀ g, 0 ≤ σ g`
  and `hσ : ∀ g h, σ (g * h) ≤ σ g + σ h`, `g : G`, `s : ℝ` and `n : ℕ`,
  `(1 + σ (g ^ n)) ^ s ≤ (1 + σ 1 + σ g) ^ |s| * (1 + n) ^ ⌈|s|⌉₊`.
- `exists_apply_eq_smul_of_pow_apply_eq_zero`: for a complex vector space `W`,
  `T : Module.End ℂ W`, `μ : ℂ`, `y` with `hy : y ≠ 0` and `k : ℕ` with
  `hk : ((T - μ • 1) ^ k) y = 0`, there is `w ≠ 0` with `T w = μ • w`.

### Stable pairings and tempered coefficients

From here on `G` is a topological group, `ρ : Representation ℂ G V` on a complex vector space
`V`, `[v]` denotes `Jacquet.mk ρ Nbar v` and `ℓ` ranges over the Library's `SmoothDual ρ`.

- `norm_le_of_stablePairing_eigenvector` (derived): `hρ : IsSmooth ρ`,
  `D : StablePairingData G`, `hA : D.Admits ρ hρ`, `v` with
  `hv : Jacquet.mk ρ D.Nbar v ≠ 0`, `ν : ℂ` with
  `hν : ∀ r : ℕ, Jacquet.mk ρ D.Nbar (ρ (D.g⁻¹ ^ r) v) = ν ^ r • Jacquet.mk ρ D.Nbar v`, `c`
  with `hc : 0 < c`, and
  `hgrowth : ∀ ℓ, ∃ (C : ℝ) (k : ℕ), ∀ᶠ r : ℕ in atTop,
  ‖smoothDualPairing ρ ℓ (ρ (D.g⁻¹ ^ r) v)‖ ≤ C * c ^ r * (1 + r) ^ k`.
  Conclusion: `‖ν‖ ≤ c`.
- `norm_le_one_of_hasTemperedCoefficients` (the bound on `|χ(a)|` in the proof of (i) ⇒ (ii),
  for one element). Hypotheses: `hρ`, `Ξ σ`, `hT`, `hΞ0`, `hσ0`, `hσ`, `Nbar M`, `hMNbar`, `δ` as
  in the next item; `m : M` with
  `hD : ∃ D : StablePairingData G, D.Nbar = Nbar ∧ D.g = (m : G)⁻¹ ∧ D.Admits ρ hρ` and
  `hΞ : ∃ (C : ℝ) (d : ℕ), ∀ r : ℕ, 1 ≤ r →
  Ξ ((m : G) ^ r) ≤ C * NNReal.sqrt (δ (m ^ r)) * (1 + σ ((m : G) ^ r)) ^ d`;
  `y : Coinvariants ρ Nbar` with `hy : y ≠ 0`, `μ : ℂ`, `k : ℕ` with
  `hk : ((normalizedActionOfModulus ρ Nbar M hMNbar δ m - μ • 1) ^ k) y = 0`.
  Conclusion: `‖μ‖ ≤ 1`. The source's corresponding step is the bound
  `|χ(a)| ⩽ c(1 + σ(a))^d` on the cone `|α(a)|_F < ε`.
- `norm_le_one_of_mem_openChamber` (the same bound on the open chamber): the hypotheses `hρ`,
  `hT`, `hΞ0`, `hσ0`, `hσ`, `hMNbar`, `δ`, `j`, `hHM`, `hD`, `hΞ` of the next item (with `E` any
  real vector space and no spanning, independence or `a₀` hypothesis), `a` with
  `ha : ∀ α ∈ S, 0 < α (HM a)`, `y ≠ 0` (`hy`), `μ : ℂ` and `k` with
  `hk : ((normalizedActionOfModulus ρ Nbar M hMNbar δ (j a) - μ • 1) ^ k) y = 0`.
  Conclusion: `‖μ‖ ≤ 1`.
- `mem_closedPositiveCone_of_hasTemperedCoefficients` (Proposition III.2.2, (i) ⇒ (ii), abstract
  form). Hypotheses:
  - `hρ : IsSmooth ρ`; `Ξ σ : G → ℝ` with `hT : HasTemperedCoefficients Ξ σ ρ`,
    `hΞ0 : ∀ g, 0 ≤ Ξ g`, `hσ0 : ∀ g, 0 ≤ σ g` and
    `hσ : ∀ g h, σ (g * h) ≤ σ g + σ h`;
  - subgroups `Nbar M : Subgroup G` with `hMNbar : M ≤ Subgroup.normalizer Nbar`, and
    `δ : M →* ℝ≥0ˣ`;
  - a commutative group `A`, `j : A →* M`, a finite-dimensional real vector space `E`
    (`[FiniteDimensional ℝ E]`), `HM : A → E` with `hHM` and `hspan` as above, `S` with `hS`,
    `a₀` with `ha₀` as above;
  - `hD : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ∃ D : StablePairingData G,
    D.Nbar = Nbar ∧ D.g = ((j a : M) : G)⁻¹ ∧ D.Admits ρ hρ`;
  - `hΞ : ∃ (C : ℝ) (d : ℕ), ∀ a, (∀ α ∈ S, 0 < α (HM a)) →
    Ξ (j a) ≤ C * NNReal.sqrt (δ (j a)) * (1 + σ (j a)) ^ d`;
  - `χ : A →* ℂˣ`, `y : Coinvariants ρ Nbar` with `hy : y ≠ 0`, and
    `hχ : ∀ a, ∃ k : ℕ, ((normalizedActionOfModulus ρ Nbar M hMNbar δ (j a) - (χ a : ℂ) • 1) ^ k) y = 0`;
  - `q` with `hq : 1 < q`, and `lam : Module.Dual ℝ E` with
    `hlam : ∀ a, ‖(χ a : ℂ)‖ = q ^ (-lam (HM a))`.

  Conclusion: `lam ∈ closedPositiveCone S`, i.e. `Re(χ) ∈ +ā_P^{G*}` under the dictionary
  above.

### Coverage and what is not covered

- For `GL_n` the Library already has the full exponent criterion
  `Langlands.glTemperedExponentCriterion` (proving
  `Langlands.GLTemperedExponentCriterionStatement`, with exponents tested on the closed negative
  block-scalar chamber) and its necessity half `Langlands.GeneralTemperedExponentNecessity.upperBound`.
  This module does not use them; it treats abstract data.
- Lemme III.2.1 (the union and the sum of the `A(π)` over tempered admissible `π`) is in the
  Library module `AdmissibleCoefficientSpace` (`temperedCoefficient_iff`,
  `exists_tempered_coefficient_add`), and Lemme III.2.3 (induction preserves temperedness) is in
  the Library module `InducedTemperedCoefficients`.
- Not formalized: (ii) ⇒ (i), (ii) ⇔ (iii), the obligations listed above, and the passage from
  Théorème I.4.1 for an actual parabolic subgroup to `hD`.

## Proof

`abs_natCast_mul_sub_le` expands `H` in the basis `b`; the difference is
`∑_i fract(n b.repr H i) φ(b i)`, bounded termwise since `0 ≤ fract < 1`.

`nonneg_of_forall_mem_openChamber`: choose a basis `b` of `E` inside `Λ`
(`exists_linearIndependent` and `Module.Basis.mk`). If `lam H < 0`, take
`n > ∑_{α ∈ S} B(α)/α(H) + B(lam)/(−lam(H))` with `B(φ) = ∑_i |φ(b i)|`. The point
`x = ∑_i ⌊n b.repr H i⌋ b_i` lies in `Λ`, and the previous lemma gives `α(x) > 0` for every
`α ∈ S` and `lam(x) < 0`, contradicting `h`.

`nonneg_of_forall_openChamber`: if `lam H < 0`, the point `H + t H₀` with
`t = −lam(H)/(2(|lam(H₀)| + 1))` lies in the open chamber and `lam(H + t H₀) < 0`.

`mem_closedPositiveCone_of_nonneg`: the map `L : E → (S → ℝ)`, `H ↦ (α(H))_α`, is surjective,
since its dual map is injective (`LinearMap.dualMap_injective_iff`) by linear independence of
`S`. Choose `H_β` with `α(H_β) = [α = β]` for `α, β ∈ S` and put `x_α = lam(H_α)` (and
`x_α = 0` off `S`); these are `≥ 0` by `h`. For any `H`, `H' = H − ∑_β β(H) H_β` is killed by every `α ∈ S`, so `h` applied to
`±H'` gives `lam(H') = 0`, hence `lam(H) = ∑_β β(H) lam(H_β)`.

`mem_closedPositiveCone_of_norm_le_one`: for `a` in the open chamber, `h1` and `hlam` give
`q^{-lam(H_M(a))} ≤ 1`, so `lam(H_M(a)) ≥ 0` as `q > 1`. Apply the density step to
`Λ = H_M(A)` (an additive subgroup by `hHM`, spanning by `hspan`), then the closure step with
`H₀ = H_M(a₀)`, then `mem_closedPositiveCone_of_nonneg`.

`le_of_eventually_pow_mul_le`: with `y = x/c`, if `y > 1` the bound gives
`y^n ≤ D (1 + n)^k` for all `n` (shifting by the threshold `N`), and the Library's
`le_one_of_pow_le` gives `y ≤ 1`, a contradiction. `one_add_rpow_le_of_subadditive` uses the
Library's `le_add_nsmul_of_subadditive` (`σ(gⁿ) ≤ σ(1) + n σ(g)`), so
`1 + σ(gⁿ) ≤ (1 + σ(1) + σ(g))(1 + n)`, and monotonicity of real powers.
`exists_apply_eq_smul_of_pow_apply_eq_zero` takes the least `n` with
`(T − μ)^n y = 0` (`Nat.find`) and `w = (T − μ)^{n−1} y`.

`norm_le_of_stablePairing_eigenvector`: let `b` be the stable pairing of the Library's
`exists_isStablePairing`. Since `[v] ≠ 0` and `b` is nondegenerate on the side of `V`
(`IsStablePairing.flip_injective`), some class `[ℓ]` of the dual has `b [ℓ] [v] ≠ 0`. By
`IsStablePairing.exists_pow_asymptotics`, `ℓ(ρ(D.g⁻¹ ^ r) v) = b [ℓ] [ρ(D.g⁻¹ ^ r) v] =
νʳ b [ℓ] [v]` for large `r`, so `|ν|^r |b [ℓ] [v]| ≤ C c^r (1 + r)^k` eventually, and
`le_of_eventually_pow_mul_le` gives `|ν| ≤ c`.

`norm_lt_one_of_norm_le_one`: if `|χ(a₀)| = 1`, then for every `b` the elements `a₀ⁿ b` and
`a₀ⁿ b⁻¹` lie in the open chamber for large `n` (`α(H_M(a₀ⁿ c)) = n α(H_M(a₀)) + α(H_M(c))`), so
`|χ(b)| = |χ(a₀ⁿ b)| ≤ 1` and `|χ(b)|⁻¹ = |χ(a₀ⁿ b⁻¹)| ≤ 1`, i.e. `|χ(b)| = 1` for all `b`,
contradicting `hne`.

`norm_le_one_of_hasTemperedCoefficients`: take `D` from `hD`. By
`exists_apply_eq_smul_of_pow_apply_eq_zero` there is a class `[v] ≠ 0` with
`π_P(m)[v] = μ[v]`; then `π_P(m^r)[v] = μ^r [v]`, and by `normalizedActionOfModulus_mk`, with
`s = δ(m)^{1/2} > 0`, `[ρ(m^r) v] = (s μ)^r [v]`, where `m^r = D.g⁻¹ ^ r`. For every `r ≥ 1`,
`hT` and `hΞ` give `|ℓ(ρ(m^r) v)| ≤ |C₁||C₂| s^r (1 + σ(m^r))^{d} (1 + σ(m^r))^{s₁}`, and both
`(1 + σ(gʳ))` factors are bounded by powers of `1 + σ(1) + σ(g)` times powers of `1 + r`
(`le_add_nsmul_of_subadditive`, `one_add_rpow_le_of_subadditive`). Now
`norm_le_of_stablePairing_eigenvector` with `ν = s μ` and `c = s` gives `s |μ| ≤ s`, i.e.
`|μ| ≤ 1`.

`norm_le_one_of_mem_openChamber` is `norm_le_one_of_hasTemperedCoefficients` for `m = j(a)` and
the data `hD a`; its growth hypothesis is `hΞ` at `a^r`, which lies in the open chamber for
`r ≥ 1` (`H_M(a^r) = r H_M(a)` by `hHM`).

`mem_closedPositiveCone_of_hasTemperedCoefficients`: by
`mem_closedPositiveCone_of_norm_le_one` it suffices to show `|χ(a)| ≤ 1` for `a` in the open
chamber, which is `norm_le_one_of_mem_openChamber` with `μ = χ(a)`.

The source argues differently after the bound `|χ(a)| ⩽ c(1 + σ(a))^d` on the cone: it writes
`Re(χ) = z + Σ_α x_α α` and evaluates the bound on the lattice `L ⊕ (⊕_α ℤNω_α)` to get
`z = 0` and `x_α ⩾ 0`. The Lean proof instead obtains `|χ(a)| ≤ 1` on the open chamber from
the powers `aʳ` and then uses density of `H_M(A)`, closure, and the dual cone of the linearly
independent family `S`. It also uses a pairing for each `a` (the data of `hD a`) and the
asymptotic formula along the powers of `a`, where the source uses one pairing on the whole cone
`|α(a)|_F < ε`.
