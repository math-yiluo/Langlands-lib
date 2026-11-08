# Root maps acting on the path weight lines

This module is an internal prerequisite for the even type `A` case of the
quasi-split Steinberg quotient task (Steinberg 1965, §9.10–9.19). Steinberg
computes with the matrices of root elements in the standard representation of
`SL_{2m+1}`. Here we work with the representation of
`Rational.PathFundamentalWeights`: a highest-weight representation whose
highest weight is the fundamental weight `lam` at the end vertex of a path
component `β` of type `A_L`. Its space is the direct sum of the `L + 1` lines
of weights `ε_j = lam - (α_0 + ⋯ + α_{j-1})`. The module shows how
torus-equivariant additive maps act on these lines, with no matrix
normalization.

- For a map of the path root `ε_i - ε_l` (`i < l`), every divided power of
  degree at least two vanishes. The first divided power maps line `l` into
  line `i` and kills every other line. So the map acts as `1 + c A₁`.
- The same holds for the negative path root `ε_l - ε_i`, with lines `i` and
  `l` exchanged.
- A map of a simple root off the path, or of its negative, acts trivially.

The simple path roots are the case `l = i + 1`. Steinberg's merged root
`α_m + α_{m+1}` is the case `l = i + 2`.

## Setting

The pure lemmas are in the namespace
`Langlands.LinearAlgebra.RootDatumPathWeights`, in the setting of that module.
`P : RootDatum ι M N`, `b : P.Base`, `β : Fin L → b.support`, and `pathWeight`
and `pathRoot` are as defined there. The divided-power lemmas are in
`Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers`, for an
actual matrix representation `σ` of the one-dimensional vector group over an
arbitrary field `k`. The representation results are in
`Langlands.GroupScheme.SplitPinning`. There `p` is a supplied split pinning of an actual affine
group scheme `G` over an arbitrary field `k`, and `ρ` is an actual
`MatrixRepresentation G n`. They concern an arbitrary additive map
`x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G` with
`hx : VectorGroup.IsTorusEquivariant p.inclusion x γ`, the Library's all-test
law `t x(c) t⁻¹ = x(γ(t) c)`. The field `torus_equivariant` of the Library's
normalized simple-root maps and of the arbitrary-root maps of
`SteinbergModifiedRootProduct` is exactly this law for the corresponding root.

## Results: shifts of path weights

- `pathWeight_sub_pathWeight`: for `l ≤ j`, `ε_l - ε_j = Σ_{t ∈ [l, j)} α_t`.
  In particular `pathRoot_eq_sub` gives `α_i = ε_i - ε_{i+1}`.
- `pathWeight_add_nsmul_sub_eq_iff`: let `IsPathComponent β`, `i < l ≤ L`,
  `j, l' ≤ L` and `m ≥ 1`. Then `ε_j + m • (ε_i - ε_l) = ε_{l'}` holds
  exactly when `m = 1`, `j = l` and `l' = i`.
- `pathWeight_add_nsmul_sub_eq_iff'`: under the same hypotheses,
  `ε_j + m • (ε_l - ε_i) = ε_{l'}` holds exactly when `m = 1`, `j = i` and
  `l' = l`.
- `pathWeight_add_nsmul_root_ne` and `pathWeight_add_nsmul_neg_root_ne`: with
  also `IsPathFundamental β ω`, let `z` be a simple root off the path and
  `m ≥ 1`. Then no `ε_j ± m α_z` is a path weight.

## Results: linear additive representations

- `coefficientMatrix_eq_zero_of_dividedPower`: a vanishing divided power has a
  vanishing coefficient matrix.
- `univariateMatrix_eq_of_dividedPower`: if `dividedPower σ m = 0` for all
  `m ≥ 2`, then the universal matrix is `1 + X • A₁`, where
  `A₁ = coefficientMatrix σ 1`.
- `affineMatrix_eq_one_add`: under the same hypothesis, for every commutative
  `k`-algebra `S` and `c ∈ S`, the actual matrix of `σ` at the vector-group
  point with coordinate `c` is `1 + c • A₁`, with entries mapped to `S`.
- `affineMatrix_eq_one`: if all positive divided powers vanish, this matrix is
  `1` at every coordinate.

## Results: root maps on the path lines

Below `hρ : p.IsHighestWeight ρ lam`, `hβ : IsPathComponent β` and
`hlam : IsPathFundamental β lam`, and `V_j` denotes
`p.representationWeightSpace ρ (pathWeight β lam j)`.

- `dividedPower_eq_zero_of_shift_ne`: suppose no `ε_j + m • γ` equals a path
  weight. Then `dividedPower (ρ.restrict x) m` kills `V_j`.
- `dividedPower_eq_zero_of_forall_shift_ne`: if this holds for every
  `j ≤ L`, the divided power is zero.
- `dividedPower_mem_of_shift_eq`: if `ε_j + m • γ = ε_l`, the divided power
  maps `V_j` into `V_l`. This needs only `hx`.
- `pathLineShiftMap` (definition): under that equation, the restriction of
  `dividedPower (ρ.restrict x) m` is a `k`-linear map `V_j →ₗ[k] V_l`.
  `pathLineShiftMap_apply` gives its underlying vector.
- For `i < l ≤ L` and `γ = ε_i - ε_l`:
  - `pathRootMap_dividedPower_eq_zero`: `dividedPower m = 0` for `m ≥ 2`.
  - `pathRootMap_dividedPower_one_mem`: `dividedPower 1` maps `V_l` into `V_i`.
  - `pathRootMap_dividedPower_one_eq_zero`: `dividedPower 1` kills `V_j` for
    every `j ≤ L` with `j ≠ l`.
- For `i < l ≤ L` and `γ = ε_l - ε_i`, the analogues are
  `negPathRootMap_dividedPower_eq_zero`, `negPathRootMap_dividedPower_one_mem`
  (`V_i` into `V_l`) and `negPathRootMap_dividedPower_one_eq_zero` (`V_j`
  killed for `j ≠ i`).
- `offPathRootMap_dividedPower_eq_zero` and
  `offPathNegRootMap_dividedPower_eq_zero`: let `z` be a simple root off the
  path and `γ = ±α_z`. Then every positive divided power vanishes, so
  `affineMatrix_eq_one` shows that `x` acts trivially.

## Proof as implemented

**Shifts.** Write `S_j = Σ_{t < j} α_t`, so `ε_j = ω - S_j`. For `j ≤ L`, a
filter computation gives `S_j = Σ_{t < L} [t < j] α_t`. The private lemma
`coeff_shift` turns
`ε_j + z • (ε_a - ε_c) = ε_{l'}` (`z ∈ ℤ`) into the coefficient equations
`[t < l'] - [t < j] + z ([t < c] - [t < a]) = 0` for all `t < L`. These follow
from linear independence of the path roots, which comes from linear
independence of the base and injectivity of `β`. The `module` tactic combines
the sums. For the positive shift, the equations at four indices give
`m = 1`, `j = l` and `l' = i`.

- At `t = i`, they give `m = 1`, `i < j` and `l' ≤ i`.
- At `t = l - 1`, they give `l ≤ j`.
- At `t = l`, if `l < L`, they give `j ≤ l`.
- At `t = i - 1`, if `i > 0`, they give `i ≤ l'`.

Each step is `split_ifs` followed by `omega`. The negative shift is the same
with the roles of `j` and `l'` exchanged. For an off-path simple root `z`,
apply the coroot of `z`. Path weights pair to zero with it
(`pairing_pathWeight_of_not_mem`), and `α_z` pairs to `2`. So `ε_j ± m α_z = ε_{l'}`
forces `2m = 0`.

**Linear representations.** The degree-`m` coefficient of the universal matrix is
`coefficientMatrix σ m` by definition. Here `A₀ = 1` (`coefficientMatrix_zero`),
`A_m = 0` for `m ≥ 2` (injectivity of `Matrix.toLin'` and
`dividedPower_eq_toLin`), and `X • C(a)` has coefficient `a` exactly in degree
one (`Polynomial.coeff_C_mul_X`). Evaluating with the published
`univariateMatrix_aeval` gives the matrix formula.

**Root maps.** By the published
`dividedPower_mem_representationWeightSpace_of_equivariant`, the divided power
maps `V_j` into the weight space of `ε_j + m • γ`. If that weight is not a path
weight, its weight space is zero by `exists_eq_pathWeight_of_isHighestWeight`.
A divided power that kills every vector of `pathWeightBasis` is zero
(`Module.Basis.ext`). The path-root and off-path statements combine this with
the shift classification above.

## Scope

The module gives no scalars. It does not show that the first divided power
between two lines is nonzero, and it does not compute reflection
representatives or torus elements in `pathWeightBasis`. It does not normalize
the basis, and it makes no statement about traces, characteristic polynomials
or class functions. These are later even type `A` obligations of the host task.
