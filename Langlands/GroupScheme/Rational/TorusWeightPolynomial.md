# Polynomial coordinate algebras of cyclic weight subgroups

Let `σ : TorusAction F I` be a split-torus action on a corepresented group functor
`F` with representing algebra `B` (`Rational.TorusGrading`), and let `U_P` be the
weight subgroups of `Rational.TorusWeightSubgroups`. This module shows that, over a
field `k`, the coordinate algebra of the cyclic weight subgroup `U_{A_r}`, for a
nonzero character `a` and the cyclic tail `A_r = {n • a : n ≥ r, n > 0}`, is a
polynomial algebra on homogeneous generators whose weights are multiples `d • a`
with `d ≥ r`. All declarations are in namespace
`Langlands.GroupScheme.Corepresented`.

## Statements

Cyclic tails and the lattice `I → ℤ`:

- `cyclicTail a r` is the subsemigroup `{χ | ∃ n, r ≤ n ∧ 0 < n ∧ n • a = χ}` of an
  additive commutative monoid (`mem_cyclicTail`). It has the same carrier as the
  Library's `RelativeRoot.cyclicTail` on character lattices.
- `nsmul_left_injective_of_ne_zero`: for `a ≠ 0` in `I → ℤ`, `n ↦ n • a` is injective
  on `ℕ`.
- `zero_notMem_cyclicTail`: `0 ∉ cyclicTail a r` for `a ≠ 0`.
- `mem_insertZero_cyclicTail`: for `a ≠ 0`, `n • a ∈ {0} ∪ cyclicTail a r` iff
  `n = 0` or `r ≤ n`.

Coordinate algebras of weight subgroups, for a subsemigroup `P`:

- `weightCorep e σ P` is the corepresentation of `U_P` (the functor
  `cutFunctor (isCutOutBy_weightIdeal e σ P)`) by `B ⧸ weightIdeal e σ P`, and
  `weightAction e σ P` is the restricted torus action on `U_P`.
- `comp_weightAction_eq_zero`: on `B ⧸ weightIdeal e σ P`, the weight components of
  weights outside `{0} ∪ P` vanish. Hence
  `mem_insertZero_of_comp_weightAction_ne_zero`: all weights lie in `{0} ∪ P`.
- `comp_zero_weightAction` and `exists_algebraMap_of_isHomogeneous_zero`: if `0 ∉ P`,
  the weight-`0` components are scalars, so the homogeneous elements of weight `0`
  are exactly the scalars.
- `weightCounit e σ P` is the counit `AffineLinearEmbedding.counit e` of `B`, factored through
  `B ⧸ weightIdeal e σ P` (the identity point lies in `U_P`).

Main theorem, for a field `k`, `B` formally smooth and of finite type over `k`, and
`a ≠ 0`:

- `exists_aeval_bijective_cyclicTail`: there are `n`, degrees `d : Fin n → ℕ` with
  `0 < d i` and `r ≤ d i`, and elements `x i` of `B ⧸ weightIdeal e σ (cyclicTail a r)`,
  homogeneous of weight `d i • a`, such that
  `MvPolynomial.aeval x : k[X_0, …, X_{n-1}] → B ⧸ weightIdeal e σ (cyclicTail a r)` is
  bijective.

Graded algebra lemma:

- `mem_span_of_mem_graded`: let `C` be an `ℕ`-graded `k`-algebra generated
  (`aeval x` surjective) by elements `x i` homogeneous of degrees `d i ≥ r`, with
  `r > 0`. Then every homogeneous element of degree `r` is a `k`-linear combination of
  the `x i` with `d i = r`.

## Proofs

For `exists_aeval_bijective_cyclicTail`, let `P = cyclicTail a r`, so `0 ∉ P`. The
weights of `C = B ⧸ weightIdeal e σ P` lie in `{0} ∪ P`, which lies in the image of the
injective map `φ = multiplesHom (I → ℤ) a : ℕ →+ (I → ℤ)`. So `gradedAlgebra hφ hsupp`
(`Rational.TorusGrading`) is an `ℕ`-grading of `C` with degree `n` part the
homogeneous elements of weight `n • a`. Its degree-`0` part is the scalars, as above.
`C` is formally smooth by `formallySmooth_quotient_weightIdeal` (`0 ∉ P`), of finite
type as a quotient of `B`, and nontrivial since `weightCounit` maps it to `k`. The
published theorem
`Langlands.Algebra.GradedFormallySmooth.exists_homogeneous_aeval_bijective` gives
`n`, positive degrees `d` and homogeneous `x` with `aeval x` bijective. Each `x i` is
nonzero (`aeval` is injective and `X i ≠ 0`), so its weight `d i • a` lies in
`{0} ∪ P`. As `d i > 0`, `mem_insertZero_cyclicTail` gives `r ≤ d i`.

For `mem_span_of_mem_graded`, write `g = aeval x p`. By
`Langlands.Algebra.GradedFormallySmooth.decompose_aeval`, `g`, being its own degree-`r`
component, is `aeval x` of the weighted homogeneous component of `p` of weight `r`.
Every monomial `m` in it has weight `r > 0`, so it contains some variable `i`, and
`weight m = r ≤ d i`. `eq_single_of_weight_le` (from the same published module) gives
`m = single i 1` and `d i = r`. So `g` is a linear combination of these `x i`.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af).
In Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 and its proof
(printed pp.111-112), the groups `U_{A_j}(G)` are smooth connected subgroups, and the
quotients `V_j = U_{A_j}(G)/U_{A_{j+1}}(G)` are shown to be vector groups by structure
theory of commutative unipotent groups (in positive characteristic via Proposition
B.4.1 and a `p`-torsion argument). This module instead takes an explicit coordinate-ring route: it
shows directly that `U_{A_r}` has a polynomial coordinate ring with homogeneous
coordinates of weights `d • a`, `d ≥ r`. The route is internal to this formalization.
