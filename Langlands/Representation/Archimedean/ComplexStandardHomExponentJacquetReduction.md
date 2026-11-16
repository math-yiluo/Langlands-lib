# Exponent shape of intertwinings from the exponents of Jacquet functionals

Lean module: `Langlands.Representation.Archimedean.ComplexStandardHomExponentJacquetReduction`
(namespace `Langlands.Archimedean`; the helper lemmas are in
`Langlands.Archimedean.ComplexStandardHomExponentJacquet`). Worker 27 wrote it for Task 7110
(`3868646b-f71b-4d18-b426-b9b18f0c8171`), whose target is the Library's
`Langlands.Archimedean.ComplexStandardHomExponentStatement` (E, module
`ComplexStandardHomExponent`). It is published as a supporting statement under Task 7178
(`9e457b4c-4441-4f77-a565-4fa8a2c37411`), so that a separate proof task can target JE.

The module contains

* the proposition `ComplexStandardJacquetExponentStatement` (JE), which is not proved here;
* the proposition `ComplexStandardHomExponentJacquetReductionStatement`, which is `JE → E`;
* the theorem `complexStandardHomExponentJacquetReduction`, which proves `JE → E`, together with
  three helper lemmas.

JE is not proved in this module, and neither is E. JE is the remaining open input for E. JE no
longer mentions intertwining maps: it is a statement about linear forms on a single principal
series.

## Notation

As in `ComplexStandardHomExponent.md`:

* a `ComplexCharacterData` `d` is the character `z ↦ (z/‖z‖)^{l} ‖z‖^{2t}` of `ℂˣ`, with weight
  `l = d.weight : ℤ` and exponent `t = d.exponent : ℂ`. In the coordinates `p = t + l/2`,
  `q = t - l/2` it is `z ↦ z^p z̄^q`;
* for `d : Fin n → ComplexCharacterData`, `X(d)` is
  `kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n)`, the
  `U(n)`-finite vectors of the principal series of `GL_n(ℂ)` normalized-induced from the upper
  triangular Borel subgroup, with right translation `complexStandardRep` and right derivatives
  `complexStandardLie`;
* `IsComplexJacquetFunctional n π ℓ a b` (module `ComplexJacquetReduction`) says that the linear
  form `ℓ` vanishes on `π(1 ⊗ X) V` for every strictly upper triangular `X`, and that
  `ℓ ∘ π(1 ⊗ E_jj) = a_j ℓ` and `ℓ ∘ π(1 ⊗ i E_jj) = b_j ℓ` for every `j`. So `ℓ` is a linear form
  on the Jacquet module `V/𝔫V` that is an eigenvector of the diagonal Cartan subalgebra, with
  weight `(a, b)`;
* `IsNonnegSimpleRootCombination u` (module `ComplexStandardHomExponent`) says that
  `u : Fin n → ℤ` is a nonnegative integer combination of the simple roots `e_k - e_{k+1}`.

**Normalization.** `ComplexJacquetReduction.md` explains it: on `X(c)`, evaluation at the
identity has the exponents `a_j = 2 t(c_j) + (n - 1) - 2j` and `b_j = i l(c_j)`. The shift
`(n - 1) - 2j` comes from `δ_B^{1/2}`. Conversely, attach to a weight `(a, b)` with `b_j ∈ iℤ` the
characters `c'_j` with `2 t(c'_j) + (n - 1) - 2j = a_j` and `i l(c'_j) = b_j`. These are the
"exponents of `ℓ`" in the classical sense, read as characters of the torus.

## Statement JE: `ComplexStandardJacquetExponentStatement`

For every `n : ℕ`, every `d : Fin n → ComplexCharacterData`, every `ℂ`-linear
`ℓ : X(d) → ℂ` and all `a b : Fin n → ℂ`, assume `ℓ ≠ 0` and
`IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b`. Then there are a
permutation `σ : Equiv.Perm (Fin n)` and `u v : Fin n → ℤ` with
`IsNonnegSimpleRootCombination u` and `IsNonnegSimpleRootCombination v` such that for every
`j : Fin n`

* `a j = 2 * (d (σ j)).exponent + ((n : ℂ) - 1) - 2 * j + (u j + v j)`, and
* `b j = Complex.I * ((d (σ j)).weight + (u j - v j))`.

**Meaning.** Let `c'` be the characters attached to `(a, b)` as in the normalization. The two
equations say `t(c'_j) = t(d_{σ j}) + (u_j + v_j)/2` and `l(c'_j) = l(d_{σ j}) + u_j - v_j`, that
is,

  `p(c'_j) = p(d_{σ j}) + u_j` and `q(c'_j) = q(d_{σ j}) + v_j`.

So the torus weights of `X(d)/𝔫X(d)` that have a nonzero eigenform are obtained from those of `d`
by one permutation `σ`, the same for both coordinates. The holomorphic coordinates `p` are then
shifted by an element `u` of the positive cone `ℕ·Δ` of the root lattice, and the antiholomorphic
coordinates `q` by an independent element `v` of `ℕ·Δ`. In particular JE implies that `b_j / i`
is an integer. JE gives a necessary condition only. It does not say which weights occur, nor
anything about multiplicities.

The Lean conclusion is written directly in terms of `a` and `b`, so it needs no characters `c'`.
Like E, JE is stated for `Fin n`-indexed characters `d` through `List.ofFn d`.

**Provenance.** Derived. JE does not appear in this form in a cited source. It is the
Jacquet-functional form of E, and the derivation of E in `ComplexStandardHomExponent.md` goes
through JE:

1. Wallach (`wallach-1979-representations-reductive-lie-groups`, 4.12 and 4.16–4.17,
   p. 77, PDF 80; 5.4, p. 78, PDF 81) defines the exponents `E(P, V)` of a module `V`
   (5.4) as the weights of the split Cartan subalgebra `𝔞` on `V/𝔫V`, shifted by `ρ_P`
   (`E(P, V) = {ν - ρ_P | ν a weight of 𝔞 on V/𝔫V}`). The
   Library's Jacquet functionals use the whole diagonal Cartan subalgebra of `𝔤𝔩_n(ℂ)` (both
   `E_jj` and `i E_jj`) and record the weight itself, without the `ρ` shift; the shift
   `(n - 1) - 2j` appears instead in the normalization above. A Jacquet functional in the sense
   of `IsComplexJacquetFunctional` is an eigenform on `V/𝔫V` for such a weight.
2. For `V = X(d)`, step 2 of the derivation of E in `ComplexStandardHomExponent.md` (the Bruhat
   filtration of the `B`-equivariant distributions on `GL_n(ℂ)` by their support on the cells
   `BwB`) concerns exactly these functionals. The cell of `w` contributes weights
   `(w·p(d) + u, w·q(d) + v)` with `u, v ∈ ℕ·Δ`. Holomorphic and antiholomorphic transversal
   derivatives give the shifts `u` and `v`. That is JE, with `σ` the permutation of `w`.

JE is in fact equivalent to E, given the Library's Frobenius reciprocity theorem
(`complexJacquetFrobenius`, proving `ComplexJacquetFrobeniusStatement` of
`ComplexJacquetFrobenius`). For the converse direction (not formalized here), take a nonzero
Jacquet functional `ℓ` on `X(d)` with weight `(a, b)`. Frobenius reciprocity gives characters `c'`
with exponents `(a, b)` and a nonzero `(𝔤, K)`-map `X(d) → X(c')`, and E applied to that map gives
JE. So JE is not stronger than E. It isolates the part that has to be proved about one
principal series.

**Consistency checks.**

* Evaluation at the identity, `ℓ = kFiniteEval _ 1` on `X(d)`, is a nonzero Jacquet functional
  with the exponents of `d` itself (`isComplexJacquetFunctional_kFiniteEval_one` below). JE holds
  with `σ = 1` and `u = v = 0`.
* The Library's swap functional (`ComplexSwapJacquet.exists_swapJacquetFunctional`, module
  `ComplexSwapJacquetFunctional`) is a nonzero Jacquet functional on the standard module of
  `pre ++ d :: e :: post` (under its hypotheses: the chart facts `ChartLieFacts`,
  `Re(t_d - t_e) ≥ 0` and a nonzero value of its integral). Its exponents are
  those of `pre ++ e :: d :: post`. JE holds with `σ` the transposition of the two positions and
  `u = v = 0`.
* Closed-cell derivatives. For `i < j` and `Y = E_ji` (a holomorphic lower triangular matrix
  unit), `f ↦ (R(Y) f)(1)` transforms under `a = diag(z)` with the extra factor `z_i / z_j`. When
  it vanishes on `𝔫X(d)`, its exponents are those of `d` with `p` shifted by the positive root
  `e_i - e_j`: `σ = 1`, `u = e_i - e_j`, `v = 0`. The same computation for the antiholomorphic
  derivative gives `v = e_i - e_j`, `u = 0`. This fixes the sign of the shifts as in E.
* `GL_2(ℂ)`, a weight that occurs. Take `d = δ_B^{-1/2}`, so `p(d) = q(d) = (-1/2, 1/2)`, and
  `c = δ_B^{1/2}`. Compose evaluation at `1` on `X(c)` with the nonzero map `X(d) → X(c)` of the
  `GL_2(ℂ)` check in `ComplexStandardHomExponent.md`. The result is a Jacquet functional on `X(d)`
  with `p = q = (1/2, -1/2)`. JE holds with `σ` the swap and `u = v = 0`, and also with `σ = 1`
  and `u = v = e_0 - e_1`.
* `GL_2(ℂ)`, a weight that JE excludes. Take `p(d) = (0, 1)` and `q(d) = (1, 0)` (that is,
  `t = (1/2, 1/2)` and `l = (-1, 1)`), and the weight `p' = q' = (0, 1)`. Up to the Weyl group it
  has the same holomorphic and the same antiholomorphic coordinates as `d`: `p' = p(d)` and `q'`
  is the swap of `q(d)`. So it passes the infinitesimal character test (Casselman–Osborne, module
  `ComplexPrincipalSeriesInfinitesimalCharacter`), but with two different permutations. JE
  excludes it. For `σ = 1`, `q' - q(d) = -(e_0 - e_1)` is not in `ℕ·Δ`. For `σ` the swap,
  `p' - σ·p(d) = (0, 1) - (1, 0) = -(e_0 - e_1)` is not in `ℕ·Δ` either. This matches the
  representation theory. The ratio of the two characters of `d` is `z^{-1} z̄`, so `X(d)` is
  irreducible. It is isomorphic to the infinite-dimensional quotient of the principal series `X(c')`
  with `p(c') = q(c') = (0, 1)`, not to a submodule of it. So there is no nonzero map
  `X(d) → X(c')`, and by Frobenius reciprocity no Jacquet functional of weight `(p', q')` on `X(d)`.
  This one permutation for both coordinates is the content of JE that the infinitesimal character
  alone does not give.

## Reduction: `ComplexStandardHomExponentJacquetReductionStatement`

`ComplexStandardHomExponentJacquetReductionStatement` is
`ComplexStandardJacquetExponentStatement → ComplexStandardHomExponentStatement`.

**Provenance.** Derived. It is step 1 of the derivation of E in `ComplexStandardHomExponent.md`:
Frobenius reciprocity in its easy direction. A `(𝔤, K)`-map `T : V → X(c)` gives the functional
`λ(v) = (T v)(1)`, which kills `𝔫V` and has the torus weight of `c·δ_B^{1/2}`. This is Wallach 1979,
4.12 (on an induced module `V(P, σ)`, evaluation at `1` is a surjective `(𝔪, K ∩ M)`-map onto
`V_σ` whose kernel contains `𝔫·V(P, σ)`) and 4.16–4.17 (the map `C` built from a quotient of
`V/𝔫V`, which is `(𝔤, K)`-equivariant), p. 77 (PDF 80). Here 4.12 is applied to `X(c)` and
composed with `T`. Wallach uses left translation and `f(kp) = δ_P(p)^{-1/2} σ(p)^{-1} f(k)`;
as in `ComplexStandardHomExponent.md`, `f ↦ (g ↦ f(g⁻¹))` turns this into the Library's
right-translation model, and evaluation at `1` is the same functional in both models.

## Proof

All results below are proved, using only standard axioms.

### Helper lemmas (namespace `ComplexStandardHomExponentJacquet`)

* `isComplexJacquetFunctional_kFiniteEval_one c`: evaluation at the identity,
  `kFiniteEval (complexStandardModule n (List.ofFn c)) 1` (module `PrincipalSeriesGKModule`), is a
  Jacquet functional on `X(c)` with exponents `a_j = 2 t(c_j) + (n - 1) - 2j` and
  `b_j = i l(c_j)`. The proof rewrites the Lie action as a right derivative
  (`ComplexSwapJacquet.coe_lie`). The derivative at `1` along a strictly upper triangular `X`
  vanishes (`ComplexSwapJacquet.rightDerivative_one_strictUpper`). Along `E_jj` and `i E_jj` it is
  `kappa · f(1)` (`ComplexSwapJacquet.rightDerivative_one_diag`), and `kappa` takes the stated
  values (`ComplexSwapJacquet.kappa_one`, `ComplexSwapJacquet.kappa_I`; module
  `ComplexSwapJacquetLie`, `ComplexSwapJacquetFunctional`). The condition `b ≤ a` of the Library
  lemma for strict upper triangularity is translated from `Fin.le` to `ℕ`.
* `isComplexJacquetFunctional_comp hT hℓ`: if `T : X(d) → X(c)` satisfies
  `IsComplexStandardIntertwining` and `ℓ` is a Jacquet functional on `X(c)` with weight `(a, b)`,
  then `ℓ ∘ T` is a Jacquet functional on `X(d)` with the same weight. The proof uses
  `IsComplexStandardIntertwining.map_lie` (module `ComplexStandardSurjectionInjectiveReduction`),
  which moves the Lie action through `T`.
* `kFiniteEval_one_comp_ne_zero hT0 hT`: if moreover `T ≠ 0`, then `(kFiniteEval _ 1) ∘ T ≠ 0`.
  Suppose `(T f)(1) = 0` for all `f`. Then for each `f` and each `k ∈ U(n)`,
  `(ρ(k)(T f))(1) = (T(ρ(k) f))(1) = 0` by `IsComplexStandardIntertwining.map_rep`. Evaluation at
  `1` separates `U(n)`-orbits (`ComplexPermutation.kFiniteEval_one_separating`, module
  `ComplexPermutationKType`, which uses the Iwasawa decomposition). Hence `T f = 0` for all `f`, a
  contradiction.

### `complexStandardHomExponentJacquetReduction`

Assume JE, and let `T : X(d) → X(c)` be nonzero with `IsComplexStandardIntertwining`. By the
three lemmas, `ℓ = (kFiniteEval _ 1) ∘ T` is a nonzero Jacquet functional on `X(d)` with weight
`a_j = 2 t(c_j) + (n - 1) - 2j`, `b_j = i l(c_j)`. JE gives `σ`, `u`, `v` with
`IsNonnegSimpleRootCombination u`, `IsNonnegSimpleRootCombination v` and, for every `j`,

* `2 t(c_j) + (n - 1) - 2j = 2 t(d_{σ j}) + (n - 1) - 2j + (u_j + v_j)`, which gives
  `t(c_j) = t(d_{σ j}) + (u_j + v_j)/2` by `linear_combination` (dividing by `2`);
* `i l(c_j) = i (l(d_{σ j}) + u_j - v_j)`, which gives `l(c_j) = l(d_{σ j}) + u_j - v_j` in `ℂ` by
  cancelling `i ≠ 0` (`mul_left_cancel₀`), and then in `ℤ` by `exact_mod_cast`.

These are the two conclusions of E for the same `σ`, `u`, `v`.

## Use

A proof of JE gives E as `complexStandardHomExponentJacquetReduction hJE`. E is an input of
Worker 729's `ComplexStandardOppositeOrderHomReduction` (Task 7055). The routes for JE in view
are those of step 2 above: the Bruhat filtration of `B`-equivariant distributions, which needs the
passage from `X(d)` to smooth vectors (automatic continuity), or the algebraic route through
category `𝒪` (Bernstein–Gelfand, `bernstein-gelfand-1980-tensor-products`, §6, 6.2–6.7,
printed pp. 280–283, PDF 37–40). That source is cited only as a possible route; it does not
state JE.
