# Finite functions on `A_M` (Waldspurger, I.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FiniteFunctionExpansion`,
namespace `Langlands.HarishChandraSchwartz`. It imports

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness`, for
  `exponentialPolynomial`, `TendstoZeroAlongParabolic` and `eq_of_tendstoZeroAlongParabolic`;
- `Langlands.HarmonicAnalysis.GroupAction`, for the right translation representation
  `rightFunctions` on all functions, `rightFunctions x f = (a ↦ f (a * x))`;
- `Langlands.Representation.IntegerLattice.GeneralizedWeightPolynomialComparisonProof` and
  `Langlands.Representation.IntegerLattice.OccurringCharactersProof`, for the lattice
  `Lattice d = Multiplicative (Fin d → ℤ)`, its generators `generator d i`, the characters
  `coordinateCharacter`, `commutingTupleGeneralizedWeightPolynomialAssembly` (Renard, Appendix
  C.III) and `coordinateCharacter_reconstruction`;
- Mathlib files for eigenspaces of commuting and semisimple endomorphisms, separable
  polynomials, polynomial-versus-geometric growth and open subgroups.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quotes from I.2 were checked on the rendered PDF pages 8 and 9; they contain
no overlines.

- I.2, printed pp. 242–243 (PDF pp. 8–9), in full: "Soit `M` un sous-groupe de Lévi
  semi-standard. Notons `ρ` l'action par translations à droite de `A_M` dans `C^∞(A_M)`. Soit
  `V` un sous-espace de `C^∞(A_M)`, stable par `ρ` et de dimension finie. Alors il existe un
  sous-ensemble fini `𝒳 ⊂ Hom(A_M, ℂ^*)` et un entier `d ∈ ℕ` tels que pour tout `f ∈ V` et
  tout `χ ∈ 𝒳`, il existe un polynôme `P_{χ,f}` sur `a_M`, à coefficients complexes et de degré
  `⩽ d`, de sorte que, pour tout `a ∈ A_M` on ait l'égalité
  `f(a) = Σ_{χ ∈ 𝒳} χ(a) P_{χ,f}(H_M(a))`.
  Supposons `𝒳` minimal, i.e. pour tout `χ ∈ 𝒳`, il existe `f ∈ V` tel que `P_{χ,f} ≠ 0`.
  Alors pour tous `χ ∈ 𝒳` et `f ∈ V`, les fonctions `a ↦ χ(a)` et
  `a ↦ χ(a) P_{χ,f}(H_M(a))` appartiennent à `V`.
  Les deux conditions suivantes sont équivalentes:
  (1) il existe `n ∈ ℕ` et, pour tout `f ∈ V`, il existe `C > 0` tel que pour tout `a ∈ A_M`,
  on ait l'inégalité `|f(a)| ⩽ C(1 + σ(a))^n`;
  (2) pour tout `χ ∈ 𝒳`, `Re(χ) = 0`.
  Soient `𝒴 ⊂ Hom(A_M, ℂ^*)` un sous-ensemble fini et `D` un entier `⩾ 1`. Supposons que pour
  tout `a ∈ A_M`, l'opérateur `Π_{χ ∈ 𝒴} (ρ(a) − χ(a))^D` annule `V`. Alors `𝒳 ⊂ 𝒴` et l'on
  peut choisir l'entier `d ⩽ D − 1`.
  Soit `f ∈ C^∞(A_M)`. Notons `V_f` le sous-espace de `C^∞(A_M)` engendré par
  `{ρ(a)f; a ∈ A_M}`. Supposons `f` `A_M`-finie, i.e. `V_f` de dimension finie. Ce que l'on a
  dit ci-dessus s'applique à `V_f`. La condition (1) pour `V_f` est équivalente à: il existe
  `n ∈ ℕ` et `C > 0` tel que pour tout `a ∈ A_M`, `|f(a)| ⩽ C(1 + σ(a))^n`."
- I.1, printed p. 240 (PDF p. 6): "Pour tout espace topologique `Z` totalement discontinu,
  notons `C^∞(Z)`, resp. `C_c(Z)`, l'espace des fonctions localement constantes, resp. à
  support compact, de `Z` dans `ℂ`." On the same page, `H_G : G → a_G` is defined by
  `q^{-⟨χ, H_G(g)⟩} = |χ|_F(g)` for `χ ∈ Rat(G)`, and "Le réseau `R` défini ci-dessus n'est
  autre que l'annulateur de `H_G(G)`. Les définitions ci-dessus s'appliquent à tout sous-groupe
  de Lévi `M`, en remplaçant `G` par `M`."
- I.1, printed p. 239 (PDF p. 5): for `χ ∈ X(G)`, `Re(χ)` is the real part of a preimage in
  `a_{G,ℂ}^*` under `χ ⊗ s ↦ (g ↦ |χ(g)|_F^s)`; "si `χ ∈ Hom(A_G, ℂ^*)`, le caractère `|χ|` se
  prolonge de façon unique en un élément de `X(G)` à valeurs réelles `> 0`. On note encore `|χ|`
  cet élément et on pose `Re(χ) = Re(|χ|)`."
- I.1, printed p. 242 (PDF p. 8): `σ(g) = log ‖g‖`, with `‖g‖ ⩾ 1` and
  `‖g_1 g_2‖ ⩽ ‖g_1‖ ‖g_2‖`.
- Lemma III.5.1, printed p. 270 (PDF p. 36), uniqueness part of the proof: "Supposons que deux
  éléments `f^w_P` et `f'^w_P` de `A^w(M)` vérifient cette condition. Fixons `m ∈ M` et
  définissons une fonction `ϕ : A_M → ℂ` par `ϕ(a) = f^w_P(ma) − f'^w_P(ma)`. Il existe `E` et
  des polynômes `Q_χ` comme ci-dessus de sorte que (1) soit vérifiée et `Re(χ) = 0` pour tout
  `χ ∈ E`." Here (1) is the expansion `ϕ(a) = Σ_{χ ∈ E} Q_χ(H_M(a)) χ(a)`.

### How the abstract data encode the source (derived; not formalized)

The group `A` is `A_M`, `E` is `a_M`, `HM` is `H_M` restricted to `A_M`, and `L` is `σ`
restricted to `A_M`; `σ ⩾ 0` and `σ(ab) ⩽ σ(a) + σ(b)` follow from the properties of `‖·‖`
quoted above. The following standard facts are used to produce the remaining hypotheses and
are not proved in this module:

- `H_M(A_M)` is a lattice in `a_M` spanning `a_M` (compare the quoted statement that `R` is the
  annihilator of `H_G(G)`). Choose a `ℤ`-basis `h_1, …, h_d` of `H_M(A_M)`, elements
  `a_i ∈ A_M` with `H_M(a_i) = h_i`, put `s(n) = Π_i a_i^{n_i}` and let `ℓ_1, …, ℓ_d` be the
  basis of `a_M^*` dual to `h_1, …, h_d`. Then `ℓ_i(H_M(s(n))) = n_i` (hypothesis `hs`), and
  since `H_M(a) = Σ_i n_i h_i` with integers `n_i`, `a s(n)^{-1} ∈ ker(H_M)` (hypothesis `hA`).
  The polynomials `Q(ℓ_1(H), …, ℓ_d(H))` are then exactly the complex polynomials on `a_M`.
- `ker(H_M) = A_M ∩ M^1` is compact (hypothesis `hcpt`), and open in `A_M`.
- A finite-dimensional `ρ`-stable `V ⊂ C^∞(A_M)` is fixed by an open subgroup `U` of `A_M`:
  for a basis `f_1, …, f_k` of `V` and points `b_1, …, b_k` with `det(f_i(b_l)) ≠ 0`, every `u`
  in an open subgroup on which all `f_i(b_l u) = f_i(b_l)` satisfies `ρ(u)f_i = f_i`, because an
  element of `V` is determined by its values at the `b_l`. In particular `f ∈ C^∞(A_M)` with
  `V_f` finite-dimensional satisfies hypothesis `hfU` of `exists_exponentialPolynomial_of_smooth`.
- A character `χ` of `A_M` with `|χ| = 1` on `ker(H_M)` has `|χ(a)| = q^{-⟨λ, H_M(a)⟩}` for
  a unique `λ ∈ a_M^*`, and `Re(χ) = λ` by the definitions quoted above. Hence `Re(χ) = 0` if
  and only if `‖χ(a)‖ = 1` for every `a`, which is how condition (2) appears in the Lean
  statements.

In the source, `d` is a degree bound; in the Lean statements `d` is the rank of the lattice
(`Lattice d`), the source's `dim a_M`.

### What is and is not formalized

Formalized (in the abstract setting above, for one function `f` and its space `V_f`):

- the expansion `f(a) = Σ_j χ_j(a) Q_j(ℓ(H_M(a)))` with finitely many characters and complex
  polynomials; for a general finite-dimensional `ρ`-stable `V`, each `f ∈ V` has
  `V_f ⊂ V`, so this applies to every element of `V`, but with characters depending on `f`;
- the direction (1) ⇒ (2) in the form "if `f` has polynomial growth, there is an expansion with
  unitary characters";
- the last sentence of I.2 in the direction "growth of `f` implies growth of every element of
  `V_f`", each element with its own constants `C` and exponent;
- the consequence used in the uniqueness part of Lemma III.5.1, quoted above.

Not formalized: a uniform degree bound `d`; minimality of `𝒳` and the membership of
`a ↦ χ(a)` and `a ↦ χ(a) P_{χ,f}(H_M(a))` in `V`; the statement (1) ⇒ (2) for a minimal `𝒳`
(the Lean statement only provides some expansion with unitary characters; uniqueness of the
expansion is not proved); the direction (2) ⇒ (1); the statement `𝒳 ⊂ 𝒴`, `d ⩽ D − 1`;
continuity of the characters `χ_j` (in the smooth form they are trivial on `U ∩ ker(H_M)`,
which in the source is open in `A_M` by the openness of `ker(H_M)` stated above, so they are
locally constant there; this step is not formalized).

## Contents

### Polynomial growth (section `Growth`)

Here `A` is a type and `L : A → ℝ` (the source's `σ`).

- `HasPolynomialGrowth L φ`, for `φ : A → ℂ`, is the proposition
  `∃ (C : ℝ) (r : ℕ), ∀ a, ‖φ a‖ ≤ C * (1 + L a) ^ r`: condition (1) of I.2 for one function.
- `hasPolynomialGrowth_zero`: `HasPolynomialGrowth L 0`.
- `HasPolynomialGrowth.add`: hypotheses `hL0 : ∀ a, 0 ≤ L a`, `HasPolynomialGrowth L φ`,
  `HasPolynomialGrowth L ψ`; conclusion `HasPolynomialGrowth L (φ + ψ)`.
- `HasPolynomialGrowth.smul`: `HasPolynomialGrowth L φ` gives `HasPolynomialGrowth L (c • φ)`
  for every `c : ℂ`.

From here on `A` is a monoid.

- `HasPolynomialGrowth.comp_mul_right`: hypotheses `hL0`, `hL : ∀ a b, L (a * b) ≤ L a + L b`,
  `HasPolynomialGrowth L φ`, and `x : A`; conclusion
  `HasPolynomialGrowth L (fun a => φ (a * x))`.
- `le_one_of_forall_pow_le`: for real `R`, `D` and `r : ℕ`, if
  `R ^ k ≤ D * (1 + k) ^ r` for every `k : ℕ`, then `R ≤ 1`.
- `norm_le_one_of_hasPolynomialGrowth`: hypotheses `hL0`, `hL`, `HasPolynomialGrowth L φ`,
  `φ ≠ 0`, `x : A`, `z : ℂ` and `hz : ∀ a, φ (a * x) = z * φ a`; conclusion `‖z‖ ≤ 1`.

### The space `V_f` (section `Translates`)

Here `A` is a commutative group and `f : A → ℂ`.

- `translateSpan f : Submodule ℂ (A → ℂ)` is the span of the right translates
  `rightFunctions x f`, `x ∈ A`: the source's `V_f`. The source's hypothesis "`f` `A_M`-finie" is
  `FiniteDimensional ℂ (translateSpan f)`.
- `mem_translateSpan_self`: `f ∈ translateSpan f`.
- `rightFunctions_mem_translateSpan`: `translateSpan f` is stable under every `rightFunctions x`.
- `translateRep f : Representation ℂ A (translateSpan f)` is the subrepresentation of
  `rightFunctions` on `translateSpan f`: the source's `ρ` on `V_f`. `translateRep_apply`:
  `(translateRep f x φ) a = φ (a * x)`.
- `hasPolynomialGrowth_of_mem_translateSpan`: hypotheses `hL0`, `hL`,
  `HasPolynomialGrowth L f` and `φ ∈ translateSpan f`; conclusion `HasPolynomialGrowth L φ`.

### The expansion (section `Expansion`)

Here `A` is a commutative group, `E` a real vector space (`[AddCommGroup E] [Module ℝ E]`, the
source's `a_M`), `HM : A → E`, `d : ℕ`, `s : Lattice d →* A` and `ℓ : Fin d → Module.Dual ℝ E`.
The recurring hypotheses are

- `hHM : ∀ a b, HM (a * b) = HM a + HM b`;
- `hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ)`;
- `hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0`.

`exponentialPolynomial HM ℓ χ Q a` is the Library's
`∑ j, (χ j a : ℂ) * MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q j)` for characters
`χ j : A →* ℂˣ` and `Q j : MvPolynomial (Fin d) ℂ`, the right-hand side of the expansion of I.2.

Auxiliary statements (derived):

- `apply_mul_eq_of_mem_translateSpan`: if `∀ a, f (a * x) = f a`, then
  `∀ a, φ (a * x) = φ a` for every `φ ∈ translateSpan f`.
- `exists_latticeCoordinate`: under `hHM`, `hs`, `hA` there is `nH : A →* Lattice d` with
  `((nH a).toAdd i : ℝ) = ℓ i (HM a)` for all `i` and `HM (a / s (nH a)) = 0`, for every `a`.
- `exponentialPolynomial_comp_equiv`: reindexing `χ` and `Q` along an equivalence `e : κ' ≃ κ`
  of finite types does not change `exponentialPolynomial HM ℓ χ Q`.
- `exponentialPolynomial_append`: for families indexed by `Fin n₁` and `Fin n₂`, the exponential
  polynomial of `Fin.append χ₁ χ₂`, `Fin.append Q₁ Q₂` is the sum of the two.
- `exponentialPolynomial_neg`: replacing every `Q j` by `-Q j` negates the value.

Main statements:

- `exists_exponentialPolynomial_of_finiteDimensional` (I.2, the expansion). Hypotheses: `hHM`,
  `hs`, `hA`, `f : A → ℂ`, `hf : FiniteDimensional ℂ (translateSpan f)` and
  `hfin : ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ ∀ a, f (a * c ^ N) = f a`. Conclusion: there are
  `n : ℕ`, `χ : Fin n → A →* ℂˣ` and `Q : Fin n → MvPolynomial (Fin d) ℂ` such that, for every
  `j`,
  - `‖(χ j c : ℂ)‖ = 1` for every `c` with `HM c = 0`;
  - `χ j c = 1` for every `c` with `HM c = 0` and `∀ a, f (a * c) = f a`;
  - for every `i` there is `φ ∈ translateSpan f`, `φ ≠ 0`, with
    `φ (a * s (generator d i)) = χ j (s (generator d i)) * φ a` for all `a`;

  and `f a = exponentialPolynomial HM ℓ χ Q a` for every `a`.
- `exists_unitary_exponentialPolynomial_of_hasPolynomialGrowth` (I.2, (1) ⇒ (2) in the form
  above). Hypotheses: `hHM`, `hs`, `hA`, `L : A → ℝ` with `hL0 : ∀ a, 0 ≤ L a` and
  `hL : ∀ a b, L (a * b) ≤ L a + L b`, `hf`, `hfin` as above, and
  `hgr : HasPolynomialGrowth L f`. Conclusion: there are `n`, `χ`, `Q` with
  `‖(χ j a : ℂ)‖ = 1` for all `j`, `a`, and `f a = exponentialPolynomial HM ℓ χ Q a` for every
  `a`.
- `exists_pow_mem_of_isCompact`: in a topological group `A`
  (`[TopologicalSpace A] [IsTopologicalGroup A]`), for subgroups `K`, `U` with `K` compact,
  `U` open and `c ∈ K`, there is `N > 0` with `c ^ N ∈ U`.
- `exists_pow_mul_eq_of_isCompact` (needs only `[AddCommGroup E]`): in a topological group `A`,
  hypotheses `hHM`, `hcpt : IsCompact {c : A | HM c = 0}`, a subgroup `U` with
  `hU : IsOpen (U : Set A)`, `f : A → ℂ` with `hfU : ∀ u ∈ U, ∀ a, f (a * u) = f a`, and `c` with
  `HM c = 0`. Conclusion: `∃ N : ℕ, 0 < N ∧ ∀ a, f (a * c ^ N) = f a`, the hypothesis `hfin`.
- `exists_exponentialPolynomial_of_smooth` (I.2 for `f ∈ C^∞(A_M)`, the expansion). In a
  topological group `A`, hypotheses `hHM`, `hs`, `hA`, `hcpt`, `U` with `hU`, `f` with `hfU` and
  `hf`. Conclusion: there are `n`, `χ`, `Q` such that for every `j`, `‖(χ j c : ℂ)‖ = 1` when
  `HM c = 0`, `χ j u = 1` for every `u ∈ U` with `HM u = 0`, and the eigenvalue clause of
  `exists_exponentialPolynomial_of_finiteDimensional` holds; and
  `f a = exponentialPolynomial HM ℓ χ Q a` for every `a`.

Application to Lemma III.5.1. Here `M` is a monoid (the source's Levi subgroup `M`) and
`j : A →* M` (the inclusion of `A_M`; the product `ma` is `m * j a`), and `C : Set (M → ℂ)`
(the source's `A^w(M)`), with the hypotheses

- `hCfin : ∀ g ∈ C, ∃ W : Submodule ℂ (M → ℂ), FiniteDimensional ℂ W ∧ g ∈ W ∧
  ∀ x : A, ∀ w ∈ W, (fun y => w (y * j x)) ∈ W`;
- `hCinv : ∀ g ∈ C, ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ ∀ y, g (y * j (c ^ N)) = g y`;
- `hCgr : ∀ g ∈ C, ∀ m, HasPolynomialGrowth L (fun a => g (m * j a))`.

- `exists_unitary_exponentialPolynomial_sub`: hypotheses `j`, `hHM`, `hs`, `hA`, `L` with `hL0`
  and `hL`, `C` with `hCfin`, `hCinv`, `hCgr`. Conclusion: for all `g₁ g₂ ∈ C` and every
  `m : M` there are `n`, `χ : Fin n → A →* ℂˣ` with `‖(χ i a : ℂ)‖ = 1` for all `i`, `a`, and
  `Q : Fin n → MvPolynomial (Fin d) ℂ` with
  `g₁ (m * j a) - g₂ (m * j a) = exponentialPolynomial HM ℓ χ Q a` for every `a`. This is the
  quoted sentence "Il existe `E` et des polynômes `Q_χ` [...] `Re(χ) = 0` pour tout `χ ∈ E`",
  and the hypothesis `hexp` of the Library's `eq_of_tendstoZeroAlongParabolic`.
- `eq_of_tendstoZeroAlongParabolic_of_mem` (uniqueness in Lemma III.5.1 for the class `C`).
  Hypotheses: `j`, `hHM`, a finite set `S : Finset (Module.Dual ℝ E)` (the source's `Σ(P)`),
  `a₀ : A` with `ha₀ : ∀ α ∈ S, 0 < α (HM a₀)`, `hs`, `hA`, `L` with `hL0` and `hL`, `C` with
  `hCfin`, `hCinv`, `hCgr`, functions `F f₁ f₂ : M → ℂ` with `f₁ ∈ C`, `f₂ ∈ C`, and for
  `i = 1, 2`,
  `∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f_i (m * j a))`. Conclusion:
  `f₁ = f₂`. `TendstoZeroAlongParabolic HM S` is the limit `lim_{a →_P ∞}` of III.5
  (`WeakConstantTermUniqueness`); in the source `F(g) = δ_P(g)^{-1/2} f(g)`.

Why the source's `A^w(M)` satisfies `hCfin`, `hCinv` and `hCgr` (derived sketch; not
formalized): an element `g ∈ A^w(M)` is a coefficient `y ↦ ⟨π(y)v, v̌⟩` of an admissible
representation `π` of `M` with `v` fixed by an open compact subgroup `K'`. Since `A_M` is
central in `M`, `π(A_M)` preserves the finite-dimensional space `V^{K'}`, and the coefficients
`y ↦ ⟨π(y)w, v̌⟩`, `w ∈ V^{K'}`, form a space `W` as in `hCfin`. For `c ∈ ker(H_M)`, compact,
some `c^N` lies in `K' ∩ A_M` and fixes `v` (`hCinv`). The bound
`|g(y)| ⩽ c' Ξ^M(y)(1 + σ(y))^r` of `A^w(M)` with `Ξ^M(ma) = Ξ^M(m)` for `a ∈ A_M` and
`σ(ma) ⩽ σ(m) + σ(a)` gives `hCgr` with `L = σ` on `A_M`.

## Proof

`le_one_of_forall_pow_le` compares `R^k` with `(1 + k)^r` using
`isLittleO_pow_const_const_pow_of_one_lt`: for `R > 1`, eventually
`k^r ≤ R^k / (2^r (|D| + 1))`, and then `R^k ≤ |D| / (|D| + 1) · R^k < R^k`.
`norm_le_one_of_hasPolynomialGrowth` picks `b` with `φ(b) ≠ 0`; then
`‖z‖^k ‖φ(b)‖ = ‖φ(b x^k)‖ ≤ C (1 + L(b) + k L(x))^r ≤ C (1 + L(b) + L(x))^r (1 + k)^r`.
`hasPolynomialGrowth_of_mem_translateSpan` is by induction on the span, using
`comp_mul_right`, `add` and `smul`.

`exists_latticeCoordinate` chooses for each `a` an `n(a)` from `hA`; `hs` and `hHM` give
`ℓ_i(H_M(a)) = n(a)_i`, which determines `n(a)` and makes `a ↦ n(a)` a homomorphism.

`exists_exponentialPolynomial_of_finiteDimensional`:

1. With `nH` from `exists_latticeCoordinate`, `cH(a) = a / s(nH(a))` is a homomorphism
   `A → A` with values in `ker(H_M)`, equal to the identity on `ker(H_M)` and trivial on
   `s(Lattice d)`.
2. By `hfin` and `apply_mul_eq_of_mem_translateSpan`, each `c ∈ ker(H_M)` has
   `translateRep f c ^ N = 1` for some `N > 0`. So `translateRep f c` is annihilated by the
   separable, hence squarefree, polynomial `X^N − 1` and is semisimple.
3. The commuting family `translateRep f (cH a)`, `a ∈ A`, has `V_f` as the sum of its joint
   maximal generalized eigenspaces (Mathlib's
   `iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`), which are
   joint eigenspaces by semisimplicity. Write `f = Σ_μ F_μ` (finitely many `μ : A → ℂ`) with
   `translateRep f (cH a) F_μ = μ(a) F_μ`. For `F_μ ≠ 0`, `μ` is a character `X_μ : A →* ℂˣ`;
   `μ(c)^N = 1`, hence `‖μ(c)‖ = 1`, on `ker(H_M)`; `μ = 1` on `s(Lattice d)`; and `μ(c) = 1`
   when `f` is invariant under `c ∈ ker(H_M)`.
4. The lattice part: `translateRep f ∘ s` is a representation of `Lattice d` on the
   finite-dimensional `V_f`. The Library's `commutingTupleGeneralizedWeightPolynomialAssembly`
   (Renard, Appendix C.III) gives a finite set `S` of tuples `w ∈ (ℂˣ)^d`, each with nonzero
   generalized weight block, such that for every vector `v`, linear form `ev` and `n`,
   `ev(translateRep f (s n) v) = Σ_{w ∈ S} w(n) · P_{w,v,ev}(n)` with
   `w(n) = coordinateCharacter w n = Π_i w_i^{n_i}` and polynomials `P_{w,v,ev}`.
5. With `v = F_μ` and `ev` the evaluation at `1`:
   `F_μ(a) = (translateRep f (s(nH a)) (translateRep f (cH a) F_μ))(1)
   = μ(a) Σ_{w ∈ S} w(nH(a)) P_{w,F_μ,ev}(nH(a))`, and `nH(a)_i = ℓ_i(H_M(a))`. Summing over
   `μ`, `f` is the exponential polynomial with characters `X_μ · (w ∘ nH)` indexed by the pairs
   `(μ, w)`, reindexed by `Fin` with `exponentialPolynomial_comp_equiv`.
6. Since `w ∘ nH` is trivial on `ker(H_M)`, the first two clauses come from step 3. For the
   eigenvalue clause, `(X_μ · (w ∘ nH))(s(e_i)) = w_i`, and `w_i` is a generalized eigenvalue,
   hence an eigenvalue, of `translateRep f (s(e_i))` because the generalized weight block of
   `w` is nonzero.

`exists_unitary_exponentialPolynomial_of_hasPolynomialGrowth`: an eigenvector `φ` from the
eigenvalue clause has polynomial growth (`hasPolynomialGrowth_of_mem_translateSpan`), so
`norm_le_one_of_hasPolynomialGrowth` applied to the translations by `s(e_i)` and by `s(e_i)^{-1}`
gives `‖χ_j(s(e_i))‖ ≤ 1` and `‖χ_j(s(e_i))^{-1}‖ ≤ 1`. So `‖χ_j(s(e_i))‖ = 1`, hence
`‖χ_j ∘ s‖ = 1` (`coordinateCharacter_reconstruction`), and with `‖χ_j‖ = 1` on `ker(H_M)` and
`hA`, `‖χ_j(a)‖ = 1` for every `a`.

`exists_pow_mem_of_isCompact`: `U ∩ K` is an open subgroup of the compact group `K`, hence of
finite index (`Subgroup.quotient_finite_of_isOpen`), and an element of a group has a positive
power in any subgroup of finite relative index (`Subgroup.exists_pow_mem_of_relIndex_ne_zero`).
`exists_pow_mul_eq_of_isCompact` applies it to the subgroup `ker(H_M)`, and
`exists_exponentialPolynomial_of_smooth` feeds the result into the main theorem as `hfin`.

`exists_unitary_exponentialPolynomial_sub`: for `g ∈ C` and `m`, the space `translateSpan` of
`a ↦ g(m j(a))` lies in the image of `W` under `w ↦ (a ↦ w(m j(a)))`, so it is
finite-dimensional, and `hCinv`, `hCgr` give `hfin` and `hgr`; the previous theorem expands
`g₁(m j(·))` and `g₂(m j(·))` with unitary characters, and the difference is the exponential
polynomial of the appended families (`exponentialPolynomial_append`,
`exponentialPolynomial_neg`). `eq_of_tendstoZeroAlongParabolic_of_mem` is the Library's
`eq_of_tendstoZeroAlongParabolic` with this `hexp`.
