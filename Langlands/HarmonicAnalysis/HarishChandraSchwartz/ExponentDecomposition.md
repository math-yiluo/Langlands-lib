# Exponents, and the weak and positive parts of a coefficient (Waldspurger I.3, III.3, VI.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDecomposition`, namespace
`Langlands.HarishChandraSchwartz`. It imports `Langlands.HarmonicAnalysis.GroupAction` (for the
right translation representation `GroupAction.rightFunctions` on `M → ℂ`, with
`rightFunctions g f x = f (x * g)`), `Mathlib.LinearAlgebra.Eigenspace.Pi` (simultaneous
generalized eigenspaces of commuting endomorphisms) and
`Mathlib.Analysis.Complex.Polynomial.Basic` (`ℂ` is algebraically closed).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Calligraphic letters in the quotes below were checked on the rendered PDF pages
9, 33, 63, 64 and 66.

- I.3, printed p. 243 (PDF p. 9): "Soit `(π, V)` une représentation admissible de `G`. Pour
  `χ ∈ Hom(A_G, ℂ^*)`, posons `V_χ = {v ∈ V; ∃d ∈ ℕ, ∀a ∈ A_G, (π(a) − χ(a))^d v = 0}`. On
  appelle exposant de `π` un caractère `χ` tel que `V_χ ≠ 0`. On note `𝓔xp(π)` l'ensemble de ces
  exposants. On a l'égalité `V = ⊕_{χ ∈ 𝓔xp(π)} V_χ`."
- III.3, printed p. 267 (PDF p. 33): "Soient `(π, V)` une représentation admissible tempérée de
  `G` et `P = MU` un sous-groupe parabolique semi-standard de `G`. On décompose le module de
  Jacquet `(π_P, V_P)` en une somme directe `(π_P, V_P) = (π^w_P, V^w_P) ⊕ (π^+_P, V^+_P)` en
  posant `V^w_P = ⊕_{χ ∈ 𝓔xp(π_P); Re(χ)=0} V_{P,χ}`, `V^+_P = ⊕_{χ ∈ 𝓔xp(π_P); Re(χ)≠0} V_{P,χ}`."
- Proof of Lemma VI.2.1 (ii), printed pp. 297–298 (PDF pp. 63–64): `(I^G_P ω_B)_{P'}` "admet une
  filtration finie sur les quotients de laquelle `A_{M'}` agit par des éléments de `𝓔`"; `𝓔^w`,
  resp. `𝓔^+`, consists of the elements with `Re[(wµ)|_{A_{M'}}] = 0`, resp. `≠ 0`; "si
  `ν ∈ 𝓔^w`, `Re(sp_χ ν) = 0` donc `|(sp_χ ν)(a)| = 1`. Tandis que si `ν' ∈ 𝓔^+`,
  `Re(sp_χ ν') ∈ +ā^{G*}_{P'}` d'après la Proposition III.2.2 et `Re(sp_χ ν') ≠ 0` d'après la
  définition de `𝓔^+`, donc `|(sp_χ ν')(a)| < 1`", for "`a ∈ A_{M'}` tel que `|α(a)|_F < 1` pour
  tout `α ∈ Σ(P')`"; and "L'opérateur `b(χ)^{−1} π_{χ,P'}(sp_χ S)` [...] annule `V^+_{χ,P'}` et
  agit par l'identité sur `V^w_{χ,P'}`."
- Proof of Lemma VI.2.3, printed p. 300 (PDF p. 66): "l'opérateur `(I^G_P(ω ⊗ χ))^+_{P'}(r_χ(a))`
  est nul donc `ρ(r_χ(a))` annule `(E^G_P sp_χ ψ)^+_{P'}`", with
  `r_χ(X) = ∏_{ν ∈ 𝓔^+} (X − sp_χ ν(a))^{n(ν)}`.

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `A` (a commutative group) is the split centre `A_M` (or `A_{M'}`), `T : A →* Module.End ℂ Y`
  its action on the Jacquet module `Y = V_P`; in the coefficient part `T = J.comp j` with `J` the
  representation `π_P` of `M` and `j : A →* M` the inclusion. `jointGenEigenspace T χ` is
  `V_{P,χ}` for a function `χ : A → ℂ`. The source's `∃ d, ∀ a` is replaced by `∀ a, ∃ k`; for a
  vector of a finite-dimensional `T`-stable subspace the two agree (not formalized).
- "Unitary" (`∀ a, |χ(a)| = 1`) stands for `Re(χ) = 0`: by I.1, `|χ(a)| = q^{−⟨Re(χ), H_M(a)⟩}`
  and `H_M(A_M)` spans `a_M`, so the two conditions are equivalent (derived, not formalized).
- `exists_weak_positive_decomposition` treats one vector `y` (the class `j_P(v)`) of a
  finite-dimensional subspace `W` stable under the centre (for an admissible `π_P`, the vectors
  fixed by a compact open subgroup of `M` that fixes `y`; not formalized here) and one linear
  form `lam` (the functional `⟨·, ǰ_P̄(v̌)⟩_P`). The coefficient `m ↦ lam (J(m) y)` is the constant
  term `f_P` of a coefficient of `π`; `F^w` and `F^+` are the coefficients of the components of
  `y` in `V^w_P` and `V^+_P`, i.e. `f^w_P` and `f^+_P`.
- The hypothesis on `a₀` for the positive part, that every non-unitary `χ` with a nonzero joint
  generalized eigenvector in `W` has `|χ(a₀)| < 1`, is the inequality `|(sp_χ ν')(a)| < 1` of the
  quotation; in the source it comes from Proposition III.2.2 for `a` strictly contracting. Its
  derivation (for the character given by `jointCharacter`) is not in this module.
- The source's direct-sum statement `V = ⊕ V_χ` is used only in the form "a vector of `W` is a
  finite sum of joint generalized eigenvectors in `W`"; independence of the summands and the
  finiteness of `𝓔xp` are not stated.

## Contents

Throughout, `A` is a commutative group, `Y` a complex vector space and
`T : A →* Module.End ℂ Y`.

### Joint generalized eigenspaces

- `jointGenEigenspace T χ` (definition), for `χ : A → ℂ`: the submodule
  `⨅ a, (T a).maxGenEigenspace (χ a)`.
- `mem_jointGenEigenspace`: `y ∈ jointGenEigenspace T χ ↔ ∀ a, ∃ k : ℕ, ((T a - χ a • 1) ^ k) y = 0`.
- `commute_jointFamily T a b`: `Commute (T a) (T b)`; `commute_jointFamily_sub_smul T c d μ ν`:
  `Commute (T c - μ • 1) (T d - ν • 1)`.
- `exists_pow_apply_eigen`: for `S : Module.End ℂ Y`, `μ`, `y ≠ 0` (`hy`) and
  `hk : ((S - μ • 1) ^ k) y = 0`, there is `m` with `((S - μ • 1) ^ m) y ≠ 0` and
  `S (((S - μ • 1) ^ m) y) = μ • ((S - μ • 1) ^ m) y`.
- `eq_of_apply_eq_smul_of_pow`: for `w ≠ 0` (`hw`) with `hS : S w = ν • w` and
  `hk : ((S - μ • 1) ^ k) w = 0`, `ν = μ`.
- `apply_mem_jointGenEigenspace`: `T b` maps `jointGenEigenspace T χ` into itself.
- `map_mul_of_mem_jointGenEigenspace`: if `x ≠ 0` (`hx0`) and `x ∈ jointGenEigenspace T χ`
  (`hx`), then `χ (a * b) = χ a * χ b` for all `a b`.
- `map_one_of_mem_jointGenEigenspace`: under the same hypotheses, `χ 1 = 1`.
- `jointCharacter χ h1 hmul : A →* ℂˣ` (definition), for `h1 : χ 1 = 1` and
  `hmul : ∀ a b, χ (a * b) = χ a * χ b`, with `jointCharacter_apply`:
  `(jointCharacter χ h1 hmul a : ℂ) = χ a`. So the eigenvalue function of an exponent is a
  character, as in the source.
- `exists_sum_mem_jointGenEigenspace`: for a submodule `W` with `[FiniteDimensional ℂ W]`,
  `hW : ∀ a, ∀ x ∈ W, T a x ∈ W` and `y ∈ W` (`hy`), there is `c : (A → ℂ) →₀ Y` with
  `c χ ∈ W ⊓ jointGenEigenspace T χ` for every `χ` and `(c.sum fun _ x => x) = y`.

### Coefficients

From here on `M` is a group and `J : Representation ℂ M Y`.

- `aeval_rightFunctions_coefficient J lam g p y`: for a linear form `lam : Y →ₗ[ℂ] ℂ`, `g : M`,
  `p : ℂ[X]` and `y : Y`,
  `aeval (GroupAction.rightFunctions g) p (fun m => lam (J m y)) =
  fun m => lam (J m (aeval (J g) p y))`.
- `aeval_prod_apply_sum_eq_zero`: for `T : Module.End ℂ V`, a finset `s`, `q : ι → ℂ[X]` and
  `F : ι → V` with `aeval T (q i) (F i) = 0` for `i ∈ s`,
  `aeval T (∏ i ∈ s, q i) (∑ i ∈ s, F i) = 0`.
- `exists_eq_of_mem_roots_prod`: every root of `∏ i ∈ s, (X - C (c i)) ^ k i` is some `c i` with
  `i ∈ s`.
- `exists_weak_positive_decomposition` (with `A` a commutative group): hypotheses `J`,
  `j : A →* M`, a submodule `W` with `[FiniteDimensional ℂ W]` and
  `hW : ∀ a, ∀ x ∈ W, J (j a) x ∈ W`, `y` with `hy : y ∈ W`, and `lam : Y →ₗ[ℂ] ℂ`. Conclusion:
  there are `Fw Fp : M → ℂ` with `(fun m => lam (J m y)) = Fw + Fp` and
  - for every `a₀ : A` a monic `pw : ℂ[X]` with `‖z‖ = 1` for every root `z` and
    `aeval (GroupAction.rightFunctions (j a₀)) pw Fw = 0`;
  - for every `a₀ : A` such that every `χ : A → ℂ` with a nonzero element of
    `W ⊓ jointGenEigenspace (J.comp j) χ` and some `b` with `‖χ b‖ ≠ 1` satisfies
    `‖χ a₀‖ < 1`: a monic `pp : ℂ[X]` and `θ < 1` with `‖z‖ ≤ θ` for every root `z` and
    `aeval (GroupAction.rightFunctions (j a₀)) pp Fp = 0`.

  In the source's notation: `F^w = f^w_{P'}` is killed by `∏_{ν ∈ 𝓔^w} (ρ(a) − ν(a))^{n(ν)}`
  (roots of modulus `1`) and `F^+ = f^+_{P'}` by `ρ(r_χ(a))` (roots of modulus `< 1`), for
  `a = j(a₀)`.

## Proof

`exists_pow_apply_eigen` takes the least `n` with `(S − μ)^n y = 0` (`Nat.find`) and
`m = n − 1`. `eq_of_apply_eq_smul_of_pow`: `(S − μ)^k w = (ν − μ)^k w`, so `(ν − μ)^k = 0`.

`map_mul_of_mem_jointGenEigenspace`: from `x`, `w = (T a − χ(a))^m x ≠ 0` is an eigenvector of
`T a` for `χ(a)`; since the `T(c) − χ(c)` commute, `w` is still a joint generalized eigenvector.
From `w`, `w' = (T b − χ(b))^{m'} w ≠ 0` is an eigenvector of `T b` for `χ(b)` and still of `T a`
for `χ(a)`, and a generalized eigenvector of `T(ab)` for `χ(ab)`. Then
`T(ab) w' = T(a) T(b) w' = χ(a)χ(b) w'`, and `eq_of_apply_eq_smul_of_pow` gives
`χ(ab) = χ(a)χ(b)`. `map_one_of_mem_jointGenEigenspace` is the same lemma for `T(1) = 1`.

`exists_sum_mem_jointGenEigenspace` restricts the commuting family to `W`, applies Mathlib's
`iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute` (each
restriction is triangularizable over `ℂ`, `iSup_maxGenEigenspace_eq_top`), writes `y` as a
finitely supported sum (`Submodule.mem_iSup_iff_exists_finsupp`) and transports the summands to
`Y` with `Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`.

`aeval_rightFunctions_coefficient` expands both `aeval`s as `Σ_i p_i X^i`
(`aeval_eq_sum_range`) and uses `ρ(g)^i f (m) = f(m gⁱ)` and `J(m gⁱ) = J(m) J(g)^i`.

`exists_weak_positive_decomposition`: decompose `y = Σ_χ c(χ)` by
`exists_sum_mem_jointGenEigenspace` for `T = J.comp j`, and let `F^w`, `F^+` be the sums of the
coefficients `m ↦ lam (J(m) c(χ))` over the unitary, resp. non-unitary, `χ` in the support. For
`a₀`, choose `k_χ` with `(J(j a₀) − χ(a₀))^{k_χ} c(χ) = 0`; by
`aeval_rightFunctions_coefficient`, `(X − χ(a₀))^{k_χ}` applied to `ρ(j a₀)` kills the coefficient
of `c(χ)`, and `aeval_prod_apply_sum_eq_zero` gives the annihilation by
`p_w = ∏_{unitary} (X − χ(a₀))^{k_χ}` and `p_+ = ∏_{non-unitary} (X − χ(a₀))^{k_χ}`. The roots are
the `χ(a₀)` (`exists_eq_of_mem_roots_prod`): of modulus `1` for `p_w`, and at most
`θ = sup ‖χ(a₀)‖ < 1` over the finitely many non-unitary `χ` for `p_+`, by the hypothesis on
`a₀`.
