# Uniqueness of the expansions of finite functions on `A_M` (Waldspurger, I.2)

Author: Worker 19, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FiniteFunctionUniqueness`,
namespace `Langlands.HarishChandraSchwartz`. It imports

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FiniteFunctionExpansion` (Worker 249):
  `exponentialPolynomial`, `exponentialPolynomial_comp_equiv`, `exponentialPolynomial_append`,
  `HasPolynomialGrowth`, `hasPolynomialGrowth_zero`, `HasPolynomialGrowth.add`,
  `norm_le_one_of_hasPolynomialGrowth`, `translateSpan`, `mem_translateSpan_self`,
  `hasPolynomialGrowth_of_mem_translateSpan`, and through its imports the lattice
  `Lattice d = Multiplicative (Fin d → ℤ)` and the right translation `rightFunctions`
  (`rightFunctions b g = (a ↦ g (a * b))`, `rightFunctions_apply`);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum` (Worker 249): the
  independence `iSupIndep_jointGenEigenspace` of the joint generalized eigenspaces, and through
  `ExponentDecomposition` the eigenspaces `jointGenEigenspace T χ = ⨅ a, (T a).maxGenEigenspace (χ a)`,
  `mem_jointGenEigenspace`, `commute_jointFamily`, `apply_mem_jointGenEigenspace`,
  `exists_pow_apply_eigen` and `exists_sum_mem_jointGenEigenspace`;
- Mathlib: forward differences (`fwdDiff`, `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`),
  `MvPolynomial.funext_set`, `MvPolynomial.aeval_natDegree_le`, `MvPolynomial.comp_aeval_apply`,
  `Module.End.aeval_apply_of_hasEigenvector`, `iSupIndep.comp`,
  `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`, `iSupIndep_iff_finsetSum_eq_imp_eq`,
  `Submodule.finrank_lt_finrank_of_lt`, `Module.finBasis`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234.

I.2, printed pp. 242–243 (PDF pp. 8–9), in full: "Soit `M` un sous-groupe de Lévi semi-standard.
Notons `ρ` l'action par translations à droite de `A_M` dans `C^∞(A_M)`. Soit `V` un sous-espace de
`C^∞(A_M)`, stable par `ρ` et de dimension finie. Alors il existe un sous-ensemble fini
`𝒳 ⊂ Hom(A_M, ℂ^*)` et un entier `d ∈ ℕ` tels que pour tout `f ∈ V` et tout `χ ∈ 𝒳`, il existe
un polynôme `P_{χ,f}` sur `a_M`, à coefficients complexes et de degré `⩽ d`, de sorte que, pour
tout `a ∈ A_M` on ait l'égalité `f(a) = Σ_{χ ∈ 𝒳} χ(a) P_{χ,f}(H_M(a))`. Supposons `𝒳` minimal,
i.e. pour tout `χ ∈ 𝒳`, il existe `f ∈ V` tel que `P_{χ,f} ≠ 0`. Alors pour tous `χ ∈ 𝒳` et
`f ∈ V`, les fonctions `a ↦ χ(a)` et `a ↦ χ(a) P_{χ,f}(H_M(a))` appartiennent à `V`. Les deux
conditions suivantes sont équivalentes: (1) il existe `n ∈ ℕ` et, pour tout `f ∈ V`, il existe
`C > 0` tel que pour tout `a ∈ A_M`, on ait l'inégalité `|f(a)| ⩽ C(1 + σ(a))^n`; (2) pour tout
`χ ∈ 𝒳`, `Re(χ) = 0`. Soient `𝒴 ⊂ Hom(A_M, ℂ^*)` un sous-ensemble fini et `D` un entier `⩾ 1`.
Supposons que pour tout `a ∈ A_M`, l'opérateur `Π_{χ ∈ 𝒴} (ρ(a) − χ(a))^D` annule `V`. Alors
`𝒳 ⊂ 𝒴` et l'on peut choisir l'entier `d ⩽ D − 1`. Soit `f ∈ C^∞(A_M)`. Notons `V_f` le
sous-espace de `C^∞(A_M)` engendré par `{ρ(a)f; a ∈ A_M}`. Supposons `f` `A_M`-finie, i.e. `V_f`
de dimension finie. Ce que l'on a dit ci-dessus s'applique à `V_f`. La condition (1) pour `V_f`
est équivalente à: il existe `n ∈ ℕ` et `C > 0` tel que pour tout `a ∈ A_M`,
`|f(a)| ⩽ C(1 + σ(a))^n`."

This quotation is the one reproduced in the Library's `FiniteFunctionExpansion.md`, whose author
checked it on the rendered PDF pages 8 and 9. The present author could not open the PDF in this
session and relies on that checked quotation. The source gives no proof of these assertions;
every proof below is internal to this project. The source's conventions for `H_M`, `Re(χ)` and
`σ` are quoted in `FiniteFunctionExpansion.md` (I.1, printed pp. 239, 240 and 242).

## Encoding of the source (shared with `FiniteFunctionExpansion`)

`A` is a commutative group (the source's `A_M`), `E` a real vector space (`a_M`), `HM : A → E`
additive (`hHM`; the source's `H_M`), `ℓ : Fin d → Module.Dual ℝ E` linear forms and
`s : Lattice d →* A` a homomorphism with `hs : ∀ n i, ℓ i (HM (s n)) = n_i`. These are exactly
the data and the hypotheses `hHM`, `hs` of `FiniteFunctionExpansion`; that module explains how a
`ℤ`-basis of the lattice `H_M(A_M)` produces them. Polynomials on `a_M` are polynomials
`Q : MvPolynomial (Fin d) ℂ` in the coordinates `ℓ_i`, evaluated at
`coordinates HM ℓ a = (ℓ_i(H_M(a)))_i`. The hypothesis `hA` of `FiniteFunctionExpansion` (every
`a` lies in `ker(H_M) · s(ℤ^d)`) is not needed here: uniqueness only uses that the coordinates of
`H_M(s(n))` run through all of `ℤ^d`.

A function `f : A → ℂ` "has an expansion" (`HasFiniteExpansion HM ℓ f`) if
`f(a) = ∑_j χ_j(a) Q_j(H_M(a))` for finitely many characters `χ_j : A →* ℂˣ` and polynomials
`Q_j`. For the source's smooth `A_M`-finite functions this is `exists_exponentialPolynomial_of_smooth`
of `FiniteFunctionExpansion` (under its hypotheses `hA`, compactness of `ker(H_M)` and an open
subgroup fixing `f`); the results below take the existence of expansions as a hypothesis
(`hexp`), so they apply to any space of functions for which expansions are known.

The source's `ρ` is `rightFunctions`, and "`V` stable par `ρ`" is
`hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V`. Condition (2), `Re(χ) = 0`, appears as
`‖χ(a)‖ = 1` for all `a`, as in `FiniteFunctionExpansion` (which explains the equivalence).
Condition (1) appears with an arbitrary `L : A → ℝ` in place of `σ`, assumed nonnegative
(`hL0`) and subadditive (`hL`); for the direction (2) ⇒ (1) the coordinates of `H_M` are assumed
bounded by `C (1 + L)` (`hHL : ∃ C, ∀ a i, |ℓ_i(H_M(a))| ≤ C (1 + L(a))`). For `L = σ` on `A_M`
this is the comparison `1 + σ(a) ≍ 1 + ‖H_M(a)‖` of the source (I.1 (6) for `M_0`), which is not
proved in this module.

## Source correction: the assertion `𝒳 ⊂ 𝒴`, `d ⩽ D − 1` is false as printed

The hypothesis "for every `a`, `Π_{χ ∈ 𝒴} (ρ(a) − χ(a))^D` kills `V`" only gives, for an exponent
`χ` and each single `a`, some `ψ ∈ 𝒴` with `ψ(a) = χ(a)`; the `ψ` may depend on `a`, because a
group can be a union of three proper subgroups.

- **`𝒳 ⊄ 𝒴`.** Take `A = ℤ²` (for instance the valuations of `A_M = (F^×)²`, a split torus of
  rank 2, all functions below being smooth on `A_M`), `H_M` the identity coordinates, `V` the
  constant functions, `D = 1` and `𝒴 = {ψ₁, ψ₂, ψ₃}` with `ψ₁(n) = (−1)^{n₀}`,
  `ψ₂(n) = (−1)^{n₁}`, `ψ₃(n) = (−1)^{n₀ + n₁}`. Every `n` lies in the kernel of one `ψ_i` (if
  `n₀` and `n₁` are odd, `n₀ + n₁` is even), so `Π_i (ρ(a) − ψ_i(a))` acts on constants by
  `Π_i (1 − ψ_i(a)) = 0`. The minimal `𝒳` is `{1}` (the coefficient of `1` in the constant
  function `1` is the polynomial `1`), and `1 ∉ 𝒴`. This is the Lean theorem
  `exists_exponent_not_mem_of_prod_annihilates`.
- **`d ⩽ D − 1` fails.** With the same `A`, take `𝒴 = {1, ψ₁, ψ₂, ψ₃}` and `V` the polynomials of
  degree `⩽ 2D − 1` in `n₀`. For every `a`, at least two characters of `𝒴` take the value `1` at
  `a`, the factors with `ψ(a) = −1` are invertible on `V`, and `(ρ(a) − 1)^{2D}` kills `V`; so
  the hypothesis holds, `𝒳 = {1} ⊂ 𝒴`, but `P_{1, n₀^{2D−1}}` has degree `2D − 1 > D − 1`. This
  second counterexample is explained here only; it is not formalized.

What remains true is the pointwise statement `exists_apply_eq_of_prod_annihilates` below. In the
source's applications the exponents of `V` come from an admissible representation (I.3), where
`V = ⊕_{χ ∈ 𝒴} V_χ` directly; that argument does not need the printed assertion.

## Contents

### Finite differences of polynomials (section `LinePolynomial`, any index type `ι`)

- `linePolynomial x v P : ℂ[X]` (definition): `z ↦ P(x + z v)` as a polynomial in one variable;
  `eval_linePolynomial`: `(linePolynomial x v P).eval z = P(x + z v)`;
  `natDegree_linePolynomial_le`: its degree is at most the total degree of `P`.
- `coordinateDifference h : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ` (definition): the difference
  operator `Q ↦ Q(X + h) − Q`; `eval_coordinateDifference`:
  `(coordinateDifference h Q)(y) = Q(y + h) − Q(y)`.
- `eval_linePolynomial_coordinateDifference`, `eval_linePolynomial_pow_coordinateDifference`: on a
  line of direction `h`, `coordinateDifference h` is the forward difference `Δ_[1]`.
- `eval_pow_coordinateDifference_eq_zero`: if `totalDegree Q < k`, then
  `(coordinateDifference h)^k Q` vanishes at every point.

### Terms of the expansion (section `Terms`)

- `coordinates HM ℓ a : ι → ℂ` (definition): `(ℓ_i(H_M(a)))_i`; `coordinates_mul` (under `hHM`).
- `exponentialTerm HM ℓ χ Q : A → ℂ` (definition): `a ↦ χ(a) Q(ℓ(H_M(a)))`, one term of the
  source's expansion; `exponentialPolynomial_eq_sum`: the Library's `exponentialPolynomial` is the
  sum of its terms; `exponentialTerm_add`, `exponentialTerm_smul`, `exponentialTerm_zero`,
  `exponentialTerm_sum`: linearity in `Q`.
- `rightFunctions_sub_smul_exponentialTerm`, `pow_rightFunctions_sub_smul_exponentialTerm`
  (under `hHM`): `(ρ(b) − χ(b))^k (χ · (Q ∘ H_M)) = χ(b)^k · χ · (((coordinateDifference H_M(b))^k Q) ∘ H_M)`.
- `exponentialTerm_mem_jointGenEigenspace` (under `hHM`): `χ · (Q ∘ H_M)` is in the joint
  generalized eigenspace of the right translations for the eigenvalue function `a ↦ χ(a)`.

### Uniqueness (section `Uniqueness`)

- `eq_zero_of_forall_eval_coordinates` (under `hs`): a polynomial vanishing at every
  `ℓ(H_M(a))` is zero; `eq_zero_of_exponentialTerm_eq_zero`: `χ · (Q ∘ H_M) = 0` only for `Q = 0`.
- `expansionCoeff χ Q ψ` (definition): the coefficient of `ψ` in the expansion with characters
  `χ_j` and polynomials `Q_j`, i.e. `∑_{j : χ_j = ψ} Q_j`; `expansionCoeff_eq_zero_of_notMem`,
  `exponentialPolynomial_eq_sum_expansionCoeff` (the expansion regrouped by distinct characters),
  `expansionCoeff_sumElim`, `expansionCoeff_neg`, `exponentialPolynomial_sumElim`.
- `coe_injective_units_monoidHom`: a character is determined by its complex values.
- **`expansionCoeff_eq_zero_of_exponentialPolynomial_eq_zero`** (under `hHM`, `hs`): if
  `∑_j χ_j(a) Q_j(H_M(a)) = 0` for every `a`, then `expansionCoeff χ Q ψ = 0` for every character
  `ψ`. `eq_zero_of_exponentialPolynomial_eq_zero`: for pairwise distinct `χ_j` all `Q_j` vanish.
- **`expansionCoeff_eq_of_exponentialPolynomial_eq`**: two expansions of the same function have the
  same coefficient for every character.

### The coefficients `P_{ψ,f}` (section `Coefficients`)

- `HasFiniteExpansion HM ℓ f` (definition): `f` has an expansion with characters indexed by some
  `Fin n`.
- `finiteCoeff HM ℓ f ψ` (definition): the source's `P_{ψ,f}`, the coefficient of `ψ` in a chosen
  expansion of `f`, and `0` when `f` has none.
- `finiteCoeff_eq_expansionCoeff` (under `hHM`, `hs`): for any expansion of `f` with any finite
  index type, `finiteCoeff HM ℓ f ψ = expansionCoeff χ Q ψ`; so `finiteCoeff` does not depend on
  the choice. `eq_sum_finiteCoeff`: `f = ∑_{ψ ∈ image χ} ψ · (P_{ψ,f} ∘ H_M)`;
  `finiteCoeff_eq_zero_of_notMem`.
- `HasFiniteExpansion.add`, `HasFiniteExpansion.smul`, `hasFiniteExpansion_zero`,
  `hasFiniteExpansion_sum`; `finiteCoeff_add`, `finiteCoeff_smul`, `finiteCoeff_sum`: `P_{ψ,f}` is
  linear in `f` on functions with expansions.

### Joint eigenvectors (section `JointEigenvector`, generic)

For a commutative group `A`, a complex vector space `Y` and `T : A →* Module.End ℂ Y`:

- `exists_ne_zero_forall_apply_eq_smul`: a nonzero finite-dimensional `T`-stable subspace `W`
  of `jointGenEigenspace T χ` contains `w ≠ 0` with `T a w = χ(a) w` for every `a` (stated with
  `finrank W = n` for the induction).
- `exists_eigenvector_of_inf_jointGenEigenspace_ne_bot`: the same for `W = V ⊓ jointGenEigenspace T χ`,
  `V` finite-dimensional and `T`-stable, when `W ≠ ⊥`.

### The minimal `𝒳` and a common expansion (section `FiniteSpaces`)

Here `V : Submodule ℂ (A → ℂ)` is finite-dimensional and stable under right translations (`hV`).

- `sum_filter_coe_eq`: an auxiliary regrouping identity.
- **`exponentialTerm_finiteCoeff_mem`** (under `hHM`, `hs`, `hV`): for `f ∈ V` with an expansion and
  every `ψ`, the function `a ↦ ψ(a) P_{ψ,f}(H_M(a))` belongs to `V`.
- `exists_finiteCoeff_ne_zero_iff` (with `hexp : ∀ g ∈ V, HasFiniteExpansion HM ℓ g`): `ψ` is in the
  minimal `𝒳` (some `f ∈ V` has `P_{ψ,f} ≠ 0`) if and only if `V ⊓ jointGenEigenspace ρ ψ ≠ ⊥`,
  i.e. `ψ` is an exponent, in the sense of I.3 (`ExponentDirectSum`), of the right translations on
  `V`.
- **`character_mem_of_finiteCoeff_ne_zero`** (under `hHM`, `hs`, `hV`): if `P_{ψ,f} ≠ 0` for some
  `f ∈ V` with an expansion, then `a ↦ ψ(a)` belongs to `V`.
- **`exists_common_expansion`** (with `hexp`): there are a finite set `𝒳` of characters, each with
  `P_{ψ,f} ≠ 0` for some `f ∈ V` (so `𝒳` is minimal), and `D ∈ ℕ` such that every `f ∈ V`
  satisfies `P_{ψ,f} = 0` for `ψ ∉ 𝒳`, `deg P_{ψ,f} ⩽ D` for every `ψ`, and
  `f = ∑_{ψ ∈ 𝒳} ψ · (P_{ψ,f} ∘ H_M)`. This is the first sentence of I.2 with one `𝒳` and one `d`
  for all of `V`; `FiniteFunctionExpansion` gives an expansion of each function separately.

### Polynomial growth (sections `GrowthBounds`, `PolynomialGrowth`, `GrowthEquivalence`)

- `hasPolynomialGrowth_const`, `HasPolynomialGrowth.mul` (needs `hL0`), `HasPolynomialGrowth.sum`
  (needs `hL0`).
- `exists_uniform_hasPolynomialGrowth` (needs `hL0`): in a finite-dimensional space of functions of
  polynomial growth one exponent `r` serves for all, as in condition (1).
- `hasPolynomialGrowth_eval_coordinates` (needs `hL0`, `hHL`), `hasPolynomialGrowth_exponentialTerm`
  (also a unitary `ψ`).
- **`norm_eq_one_of_hasPolynomialGrowth_of_exponent`** ((1) ⇒ (2) for exponents; needs `hL0`, `hL`,
  `hV`): if every element of `V` has polynomial growth and `V ⊓ jointGenEigenspace ρ χ ≠ ⊥`, then
  `‖χ(a)‖ = 1` for every `a`.
- `translateSpan_uniform_growth_iff` (the last sentence of I.2; needs `hL0`, `hL` and
  `FiniteDimensional ℂ (translateSpan f)`): condition (1) for `V_f` holds if and only if
  `|f(a)| ⩽ C (1 + L(a))^r` for some `r` and `C`.
- `hasPolynomialGrowth_of_unitary` ((2) ⇒ (1) for one function; needs `hHM`, `hs`, `hL0`, `hHL`):
  an `f` with an expansion whose characters with nonzero coefficient are unitary has polynomial
  growth.
- **`exists_uniform_growth_iff_unitary`** (the equivalence (1) ⇔ (2) of I.2; needs `hHM`, `hs`,
  `hL0`, `hL`, `hHL`, `hV`, `hexp`): (1) there is `r ∈ ℕ` such that every `f ∈ V` satisfies
  `‖f(a)‖ ⩽ C_f (1 + L(a))^r` if and only if (2) every `ψ` with `P_{ψ,f} ≠ 0` for some `f ∈ V`
  satisfies `‖ψ(a)‖ = 1` for all `a`. The source's `C > 0` is immaterial (replace `C` by
  `max C 1`).

### The last assertion of I.2 (section `Annihilation`)

- `aeval_apply_of_apply_eq_smul`: a polynomial `p` in `T` acts on `w` with `T w = μ w` by `p(μ)`.
- **`exists_apply_eq_of_prod_annihilates`** (corrected form; needs `hV`): write the source's operator
  `Π_{ψ ∈ 𝒴} (ρ(a) − ψ(a))^D` as `aeval (rightFunctions a) (∏_{ψ ∈ 𝒴} (X − ψ(a))^D)` (a polynomial
  in the single operator `ρ(a)`). If it kills `V` for every `a`, then for every exponent `χ` of `V`
  (`V ⊓ jointGenEigenspace ρ χ ≠ ⊥`, equivalently `χ ∈ 𝒳` under `hexp`) and every `a` there is
  `ψ ∈ 𝒴` with `ψ(a) = χ(a)`.
- `signCharacter v : Lattice 2 →* ℂˣ` (definition): `n ↦ (−1)^{v₀ n₀ + v₁ n₁}`;
  `coe_signCharacter`.
- **`exists_exponent_not_mem_of_prod_annihilates`**: the counterexample of the correction above,
  with `HM n = (n₀, n₁) ∈ ℝ²`, `ℓ` the coordinate projections, `V = ℂ · 1`, `D = 1` and
  `𝒴 = {signCharacter (1,0), signCharacter (0,1), signCharacter (1,1)}`: `V` is finite-dimensional
  and stable, the operator kills `V` for every `a`, and the trivial character is not in `𝒴` but has
  a nonzero coefficient `P_{1,1} = 1` on the element `1` of `V`.

## Proof notes

- *Generalized eigenvectors.* `pow_rightFunctions_sub_smul_exponentialTerm` is an induction on `k`
  from the case `k = 1`, a direct computation with `χ(ab) = χ(a)χ(b)` and
  `H_M(ab) = H_M(a) + H_M(b)`. On the line `y + z h`, `coordinateDifference h` becomes the forward
  difference `Δ_[1]`; the iterated difference of a one-variable polynomial of degree `< k` is zero
  (Mathlib), and the line polynomial has degree at most `totalDegree Q`
  (`MvPolynomial.aeval_natDegree_le`). So `(ρ(b) − χ(b))^{deg Q + 1}` kills `χ · (Q ∘ H_M)`.
- *Uniqueness.* The joint generalized eigenspaces of the right translations are independent
  (`iSupIndep_jointGenEigenspace`), also after composing with the injective map `ψ ↦ (a ↦ ψ(a))`.
  Regroup the expansion by distinct characters; each regrouped term lies in its own eigenspace and
  the sum is zero, so each term is zero (`iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`). A term
  `ψ · (P ∘ H_M)` vanishes only if `P` vanishes at the points `ℓ(H_M(s(n))) = n ∈ ℤ^d`, hence
  `P = 0` (`MvPolynomial.funext_set` with infinite sides `ℤ ⊂ ℂ`). Comparing two expansions
  applies this to the expansion on the sum type with the second family negated.
- *`finiteCoeff`.* It uses a chosen expansion; `finiteCoeff_eq_expansionCoeff` compares any other
  expansion with it (reindexing an arbitrary finite type by `Fin n` with
  `exponentialPolynomial_comp_equiv`). Linearity follows from uniqueness applied to concatenated
  expansions.
- *Joint eigenvector.* Strong induction on `finrank W`. If every `T a` acts on `W` by `χ(a)`, any
  nonzero vector works. Otherwise some `N = T b − χ(b)` is nonzero on `W`; `W' = W ⊓ ker N` is
  stable (the `T a` commute with `N`), strictly smaller, and nonzero: a nonzero `y ∈ W` has
  `N^k y = 0` for some `k`, and the last nonzero `N^m y` (`exists_pow_apply_eigen`) lies in `W'`.
- *Membership in `V`.* `exists_sum_mem_jointGenEigenspace` writes `f ∈ V` as a finite sum of
  vectors `c_φ ∈ V ⊓ jointGenEigenspace ρ φ`; the regrouped expansion writes `f` as a sum of terms
  in the same eigenspaces. Independence (`iSupIndep_iff_finsetSum_eq_imp_eq`) identifies the term of
  `ψ` with `c_ψ ∈ V`. For `a ↦ ψ(a)`: the joint eigenvector `w ∈ V ⊓ jointGenEigenspace ρ ψ`
  satisfies `w(a) = (ρ(a) w)(1) = ψ(a) w(1)` with `w(1) ≠ 0`, so `ψ = w(1)^{-1} w ∈ V`. The converse
  in `exists_finiteCoeff_ne_zero_iff` applies independence to `g ∈ V ⊓ jointGenEigenspace ρ ψ` and
  its regrouped expansion: if `P_{ψ,g} = 0`, then `g = 0`.
- *Common expansion.* Expand the elements of a basis of `V`; `𝒳` is the set of their characters
  with a nonzero coefficient for some element of `V`, and `D` the largest degree of their
  coefficients. Linearity of `P_{ψ,f}` (`finiteCoeff_sum`) transfers both to every `f ∈ V`;
  `Finset.sum_subset` changes the index set of the expansion of `f` to `𝒳`.
- *(1) ⇒ (2).* For an exponent `χ`, a joint eigenvector `w ∈ V` gives `w(a' x) = χ(x) w(a')`;
  `norm_le_one_of_hasPolynomialGrowth` applied to `x = a` and `x = a^{-1}` gives `‖χ(a)‖ ⩽ 1` and
  `‖χ(a^{-1})‖ ⩽ 1`, and `χ(a^{-1}) χ(a) = 1` (from `w ≠ 0`) forces `‖χ(a)‖ = 1`.
- *(2) ⇒ (1).* A polynomial in the coordinates has polynomial growth by induction on the polynomial
  (`HasPolynomialGrowth.mul` for the products with a coordinate, bounded by `hHL`); a unitary
  character does not change the norm. Uniformity of the exponent comes from a basis of `V`.
- *Annihilation.* `Module.End.aeval_apply_of_hasEigenvector` evaluates the polynomial at the
  eigenvalue `χ(a)` of a joint eigenvector, and a product of complex numbers vanishes only if a
  factor does. The counterexample checks the three parity cases with `Int.even_or_odd`,
  `Even.neg_one_zpow` and `Odd.add_odd`, and evaluates each `signCharacter` at `(1,0)` or `(0,1)`.

## Relation to the Library and to the source map

- `FiniteFunctionExpansion` proves the existence of expansions (per function) and the direction
  "(1) ⇒ some expansion with unitary characters". Its Markdown lists as not formalized: the uniform
  degree bound, minimality of `𝒳` and the two membership claims, (1) ⇒ (2) for the minimal `𝒳`
  (uniqueness), (2) ⇒ (1), and `𝒳 ⊂ 𝒴`, `d ⩽ D − 1`. This module supplies all of them except the
  printed last assertion, which is false; it supplies the corrected pointwise form and a Lean
  counterexample instead.
- `exists_finiteCoeff_ne_zero_iff` identifies the minimal `𝒳` of I.2 with the exponents of I.3
  (`exponentSet` of `ExponentDirectSum`) for the right translations on `V`.

## Not formalized here

- The derivation of `hexp`, `hHL` and the encoding data for the actual `A_M`, `H_M` and `σ` of a
  Levi subgroup (the standard facts are listed in `FiniteFunctionExpansion.md`), and the
  comparison `1 + σ(a) ≍ 1 + ‖H_M(a)‖` on `A_M`.
- A corrected degree bound (for instance under the hypothesis that `(ρ(a) − χ(a))^D` kills the
  `χ`-component of `V` for every `a`); the counterexample to `d ⩽ D − 1` above is not formalized.
