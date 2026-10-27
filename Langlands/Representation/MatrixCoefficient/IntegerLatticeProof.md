# Proof: exponential-polynomial matrix coefficients on the integer lattice

Author: Worker 219.

The module `Langlands.Representation.MatrixCoefficient.IntegerLatticeProof`
proves

```lean
theorem Langlands.integerLatticeMatrixCoefficientExponentialPolynomial :
    IntegerLatticeMatrixCoefficientExponentialPolynomialStatement.{u}
```

This is the closed statement of
`Langlands.Representation.MatrixCoefficient.IntegerLatticeStatement`. Its
universe parameter `u` is the carrier universe of `V`. The module imports that
statement, whose Lean/Markdown pair is unchanged, together with these Mathlib
modules:

- `Mathlib.Algebra.MvPolynomial.Rename`, for `MvPolynomial.rename`;
- `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`, for
  `Module.End.iSup_maxGenEigenspace_eq_top`;
- `Mathlib.LinearAlgebra.Finsupp.LinearCombination`, for
  `Submodule.mem_span_set'`;
- `Mathlib.Analysis.Complex.Polynomial.Basic`, for the instance
  `IsAlgClosed ℂ`.

The development check reports no errors or warnings. The theorem depends only
on `propext`, `Classical.choice` and `Quot.sound`. No hypothesis is added: the
proof holds for every `d`, including `d = 0`, for every finite-dimensional `V`,
including the zero space, and for every `v` and every `ell`. It is valid at all
integer tuples, negative coordinates included.

## Source and route

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, Appendix C.III, printed pp.279–280
(one-based PDF pp.285–286). The literature ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Both pages
were read. The statement Markdown records the errata check. The 2010
correction concerns parentheses in Renard's displayed expansion. This proof
does not use that formula.

Renard's proof picks a common triangular basis adapted to the simultaneous
generalized eigenspaces. On each block he writes every generator as
`z (Id + N)` with `N` strictly upper triangular, and multiplies the `d`
finite binomial expansions of the integer powers.

The Lean proof takes a different route. It needs no simultaneous
decomposition, triangular basis, or commuting nilpotent parts. The proof
inducts on `d`. Each step uses the generalized eigenspaces of a single
generator. For a generalized eigenvector, every integer power is a finite
binomial expansion. The proof checks this through Pascal's rule and an
injectivity argument, not through a binomial theorem for negative exponents.
The steps are below.

### 1. Binomial coefficients as polynomial functions

`binomCoeff k x` is defined as `(k!)⁻¹ * ∏ i ∈ range k, (x - i)` for complex
`x`. Three lemmas give its values and recursion:

- `binomCoeff_zero`: `binomCoeff 0 x = 1`;
- `binomCoeff_succ_zero`: `binomCoeff (k + 1) 0 = 0`;
- `binomCoeff_succ_succ`: Pascal's rule
  `binomCoeff (k + 1) (x + 1) = binomCoeff k x + binomCoeff (k + 1) x`, for
  every complex `x` and so for every integer.

`binomPoly k` is the polynomial
`C (k!)⁻¹ * ∏ i ∈ range k, (X 0 - C i)` in `MvPolynomial (Fin (d + 1)) ℂ`.
`eval_binomPoly` states that its value at `n` is `binomCoeff k (n 0)`. So the
binomial coefficient of the zeroth coordinate is an ordinary polynomial in that
coordinate. This is Renard's remark that binomial coefficients are polynomials
in the `n_i`.

### 2. One invertible operator on one generalized eigenvector

`int_seq_eq_of_step` is a general uniqueness lemma for sequences indexed by
`ℤ`. Let `T` be injective. Suppose `F` and `G` agree at `0`, and both satisfy
`F (m + 1) = T (F m)` and `G (m + 1) = T (G m)`. Then `F` and `G` agree at
every integer. The proof uses `Int.induction_on`. Upward steps use the two
recursions. Downward steps use injectivity: `T (F (m - 1)) = F m = G m =
T (G (m - 1))`.

`zpow_apply_of_genEigen` takes a unit `T` of `Module.End ℂ V`, a nonzero
`μ : ℂ`, and a vector `v` with `((T - μ • 1) ^ K) v = 0`. It sets
`M = μ⁻¹ • (T - μ • 1)` and proves, for every `m : ℤ`,

```text
(T ^ m) v = μ ^ m • ∑ k ∈ range (K + 1), binomCoeff k m • (M ^ k) v.
```

Here `T ^ m` is the integer power in the unit group, so negative `m` means
powers of the inverse. The proof applies `int_seq_eq_of_step` to the left side
`F` and the right side `G`.

- **Injectivity.** `T` is injective because `T⁻¹ * T = 1`.
- **Value at zero.** `G 0 = v`, because `binomCoeff (k + 1) 0 = 0` and
  `binomCoeff 0 0 = 1`.
- **Recursion for `F`.** `F` satisfies the recursion by `zpow_one_add`.
- **Recursion for `G`.**
  - First, `T w = μ • (w + M w)` for every `w`.
  - Second, `M ^ (K + 1)` kills `v`.
  - Write `S m` for the sum. Pascal's rule and two reindexings by
    `Finset.sum_range_succ'` give `S (m + 1) = S m + M (S m)`. Moving the
    sum's last term with `Finset.sum_range_succ` adds a term that vanishes,
    because `M ^ (K + 1)` kills `v`.
  - Together with `zpow_add_one₀`, this gives `G (m + 1) = T (G m)`.

On a generalized eigenspace, `T` is `μ (Id + M)` with `M` nilpotent. This is
Renard's scalar-times-unipotent factor `z (Id + N)`, here for a single
operator. The displayed identity is the source's finite binomial expansion of
an integer power, proved for all integers.

### 3. The span of exponential-polynomial vector functions

Let `W` be a complex vector space. `term χ Q w` is the function
`n ↦ ((χ (ofAdd n) : ℂ) * eval (fun i => (n i : ℂ)) Q) • w` on
`Fin d → ℤ`. Here
`χ : Multiplicative (Fin d → ℤ) →* ℂˣ` and `Q : MvPolynomial (Fin d) ℂ`.
`space d W` is the complex span of all such terms, inside
`(Fin d → ℤ) → W`. It is an auxiliary submodule of this proof only.

- `term_mem`: every term lies in `space d W`.
- `comp_mem`: composing with a linear map `ell : W →ₗ[ℂ] W'` maps
  `space d W` into `space d W'`. The proof uses `Submodule.span_le` and
  `LinearMap.compLeft`, together with the equality
  `ell ∘ term χ Q w = term χ Q (ell w)`.
- `exists_of_mem`: every scalar function in `space d ℂ` has exactly the
  target's form `∑ j : Fin l, (χ j (ofAdd n) : ℂ) * eval n (Q j)`. One `l`,
  `χ` and `Q` serve every `n`. `Submodule.mem_span_set'` gives a finite
  `Fin l` combination `∑ j, a j • term (χ j) (Q j) (w j)`. Each coefficient
  `a j * w j` is absorbed into the polynomial as `C (a j * w j) * Q j`.

### 4. Adjoining one coordinate

`consChar μ χ` is the character `x ↦ μ ^ (x 0) * χ (tail x)` of
`Multiplicative (Fin (d + 1) → ℤ)`, built from `μ : ℂˣ` and a character `χ`
of the smaller lattice. Its multiplicativity uses `zpow_add`, `ofAdd_add` and
commutativity of `ℂˣ`.

`cons_mem` takes `g ∈ space d W` and proves that
`n ↦ ((μ : ℂ) ^ (n 0) * binomCoeff k (n 0)) • g (Fin.tail n)` lies in
`space (d + 1) W`. The assignment is a linear map `Φ`. On a generating term,
`Φ (term χ Q w)` equals
`term (consChar μ χ) (binomPoly k * rename Fin.succ Q) w`. The proof uses
`eval_binomPoly`, `MvPolynomial.eval_rename` and
`Units.val_zpow_eq_zpow_val`. Then `Submodule.span_le` gives the claim.

### 5. Orbit maps by induction on `d`

`consZero d` is the group homomorphism from `Multiplicative (Fin d → ℤ)` to
`Multiplicative (Fin (d + 1) → ℤ)` sending `n'` to `Fin.cons 0 n'`.
`ofAdd_eq_consZero_mul` decomposes every element of the larger lattice:

```text
ofAdd n = consZero d (ofAdd (Fin.tail n)) * ofAdd (Pi.single 0 1) ^ (n 0).
```

`orbit_mem_space` states that for every finite-dimensional `V`, every
representation
`ρ : Representation ℂ (Multiplicative (Fin d → ℤ)) V` and every `v`, the orbit
map `n ↦ ρ (ofAdd n) v` lies in `space d V`. The proof inducts on `d`, with
`ρ` and `v` general.

- **`d = 0`.** Every element of the trivial lattice is `1`, and `ρ 1 = 1`.
  So the orbit map is the constant `term 1 1 v`.
- **Step from `d` to `d + 1`.** Let `ρ' = ρ.comp (consZero d)` be the
  restriction to the last `d` coordinates. Let
  `T = ρ.asGroupHom (ofAdd (Pi.single 0 1))` be the zeroth generator as a unit
  of `Module.End ℂ V`. By the decomposition above, together with `map_zpow` and
  `Representation.asGroupHom_apply`, the orbit map of `v` equals
  `L v = fun n => ρ' (ofAdd (Fin.tail n)) ((T ^ (n 0)) v)`. The map `L` is
  linear in `v`. It remains to show `⊤ ≤ (space (d + 1) V).comap L`.
  - **Eigenspace reduction.** By `Module.End.iSup_maxGenEigenspace_eq_top`
    for `T`, which needs `IsAlgClosed ℂ` and finite dimension, it suffices to
    treat each `w` in a maximal generalized eigenspace `μ`.
    `Module.End.mem_maxGenEigenspace` supplies `K` with
    `((T - μ • 1) ^ K) w = 0`.
  - **Eigenvalue zero.** If `μ = 0`, then `T ^ K` kills `w`. Since `T ^ K` is
    a unit, `w = 0`, and `L 0 = 0` lies in the submodule.
  - **Nonzero eigenvalue.** Otherwise, Step 2 rewrites `L w` as the finite
    sum over `k ∈ range (K + 1)` of
    `n ↦ ((μ : ℂ) ^ (n 0) * binomCoeff k (n 0)) •
    ρ' (ofAdd (Fin.tail n)) ((M ^ k) w)`. The induction hypothesis for `ρ'`
    and the vector `(M ^ k) w` puts each inner orbit map in `space d V`.
    `cons_mem` then puts each summand in `space (d + 1) V`.

### 6. The theorem

Given `d`, `V`, `ρ`, `v` and `ell`, `orbit_mem_space` puts the orbit map of
`v` in `space d V`. `comp_mem ell` puts `n ↦ ell (ρ (ofAdd n) v)` in
`space d ℂ`. `exists_of_mem` returns `l`, `χ` and `Q`. These witnesses are
chosen before the universal quantifier over `n`.
`matrixCoefficient ρ ell v (ofAdd n)` is definitionally
`ell (ρ (ofAdd n) v)`, so the equality is the target's at every `n`. The
characters take values in all of `ℂˣ`: each is a product of integer powers of
nonzero generalized eigenvalues, and unitarity is not used. The construction
does not ensure distinct characters or a degree bound, and the target does not
require either.

## Reuse

Only Mathlib and the target statement module are imported. The published
construction `Langlands.Representation.IntegerLattice` was inspected,
including `CommutingInvertibleTuple`, `tupleRepresentationEquiv` and
`representation_eq_product`. Its `noncommProd` description of `ρ n` is not
needed here, because the induction restricts `ρ` directly along `consZero`.
That module is therefore not imported, and its tuple correspondence is not
duplicated. Tuple-form specialization is not part of this module.
