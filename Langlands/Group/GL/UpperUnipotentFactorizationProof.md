# Proof of the plus-minus multiplication homeomorphism

Author: Worker 778.

The theorem `Langlands.GeneralLinear.upperUnipotentFactorization.{u}` proves the
published proposition
`Langlands.GeneralLinear.UpperUnipotentFactorizationStatement.{u}` of
`Langlands.Group.GL.UpperUnipotentFactorizationStatement`, with no additional
parameters or assumptions. For every field `K : Type u` with a topology making
it a Hausdorff topological division ring, every `n : ℕ` (including `0`) and
every `w : Equiv.Perm (Fin n)`, it supplies a homeomorphism

```text
e : permutationUnipotentPlus n K w × permutationUnipotentMinus n K w ≃ₜ upperUnipotent n K
```

whose value at every pair `x` has underlying matrix-unit `x.1.val * x.2.val`
in `Langlands.GeneralLinear n K`. The groups are the published actual
subgroups of `Langlands.Group.GL.UpperBruhatCells`, with their inherited
subtype and product topologies; nothing in them is changed.

## Implemented proof

All helpers live in the namespace
`Langlands.GeneralLinear.UpperUnipotentFactorization` of this module. Its
algebraic part is stated over an arbitrary commutative ring `R`, and its
topological part over a commutative ring with a topology making it a
topological ring. The final theorem instantiates them at the field `K`, whose
topological-division-ring structure supplies the topological-ring structure.
The Hausdorff hypothesis of the statement is not used.

### The factors as a fixed point of a polynomial step map

Write the plus and minus factors of an upper unipotent `u` as `1 + N` and
`1 + M`. The selectors

```text
plusPart w Z  (i, j) = Z i j  if i < j and w i < w j, else 0,
minusPart w Z (i, j) = Z i j  if i < j and w j < w i, else 0
```

keep the strictly upper entries whose order `w` preserves, respectively
reverses. The step map is

```text
step w u (N, M) = (plusPart w (u - 1 - N * M), minusPart w (u - 1 - N * M)),
```

and the strict parts of the factors are `strictParts w u = (step w u)^[n] (0, 0)`.
The factors as matrices are `plusMatrix w u = 1 + (strictParts w u).1` and
`minusMatrix w u = 1 + (strictParts w u).2`.

The predicate `StrictUpper N` says that `N` vanishes on and below the
diagonal, and `AgreeBelow m N N'` says that `N i j = N' i j` whenever
`j < i + m` (as natural numbers). Both selectors produce strictly upper
matrices. For strictly upper `N, M`, the entry `(N * M) i j` is the sum of
`N i k * M k j` over `i < k < j`; if `j < i + m + 1` then each such term has
`k < i + m` and `j < k + m`. Hence `agreeBelow_mul`: agreement below `m` of
two strictly upper pairs gives agreement below `m + 1` of their products.
Subtraction from `u - 1` and both selectors preserve agreement below `m`
(`agreeBelow_sub`, `agreeBelow_plusPart`, `agreeBelow_minusPart`), so one step
raises the agreement bound by one (`agreeBelow_step`). Two strictly upper
starting pairs agree below `0` trivially, and induction gives
`agreeBelow_iterate`: after `m` steps they agree below `m`. Agreement below `n`
is equality (`eq_of_agreeBelow`). Comparing the starting pairs `(0, 0)` and
`step w u (0, 0)` after `n` steps gives `step_strictParts`:

```text
step w u (strictParts w u) = strictParts w u,
```

for every square matrix `u`, without any hypothesis on `u`.

### The product identity

Let `u` vanish below the diagonal and have ones on it
(`plusMatrix_mul_minusMatrix_of`). Put `(N, M) = strictParts w u`. For
`i < j`, injectivity of `w` makes exactly one of `w i < w j` and `w j < w i`
true, so the fixed-point equations give
`(N + M) i j = (u - 1 - N * M) i j`. For `¬ i < j`, the entries of `N`, `M`
and (by `mul_apply_eq_zero`) of `N * M` vanish, and so does `(u - 1) i j`,
because `u` is upper unipotent. Hence `N + M = u - 1 - N * M`, and the ring
identity `(1 + N) * (1 + M) = 1 + (N + M) + N * M` (by `noncomm_ring`) gives
`plusMatrix w u * minusMatrix w u = u`. For `g : upperUnipotent n R`, this is
`plusMatrix_mul_minusMatrix`.

### The factors as subgroup elements

For `g : upperUnipotent n R`, write `P = plusMatrix w g` and
`Q = minusMatrix w g`, so `P * Q = g`. The unit `plusUnit w g` has value `P`
and inverse `Q * g⁻¹`; the unit `minusUnit w g` has value `Q` and inverse
`g⁻¹ * P`. One side of each inverse law is a direct consequence of `P * Q = g`;
the other follows from Mathlib's `mul_eq_one_comm` for square matrices over a
commutative ring.

The diagonal entries of `P` and `Q` are `1`, and the fixed-point equations
show that `P i j = 0` for `i ≠ j` unless `i < j` and `w i < w j`, and
`Q i j = 0` for `i ≠ j` unless `i < j` and `w j < w i`. The published entry
criteria `mem_upperUnipotent_iff`, `mem_permutationUnipotentPlus_iff_entries`
and `mem_permutationUnipotentMinus_iff_entries` then give `plusUnit_mem` and
`minusUnit_mem`: the units lie in `permutationUnipotentPlus n R w` and
`permutationUnipotentMinus n R w` respectively.

### The bijection

The forward map `mulMap n R w` sends `(a, b)` to the product `a.val * b.val`,
which lies in `upperUnipotent n R` by
`permutationUnipotentPlus_le_upperUnipotent`,
`permutationUnipotentMinus_le_upperUnipotent` and closure under
multiplication. The candidate inverse `factorMap n R w` sends `g` to
`(plusUnit w g, minusUnit w g)` with their membership proofs, and
`mulMap_factorMap` is the product identity. Injectivity (`mulMap_injective`)
uses the published `permutationUnipotentPlus_inf_minus`: if
`a * b = a' * b'`, then `a'⁻¹ * a = b' * b⁻¹` lies in both subgroups, hence is
`1`, so `a = a'` and `b = b'`. The left inverse law follows from injectivity
and `mulMap_factorMap`.

### Continuity

The forward map is continuous since multiplication in the topological monoid
`Langlands.GeneralLinear n R` is continuous and subtype values are continuous.
For the inverse, both selectors are continuous (each entry is a coordinate or
the constant `0`), and so `step` is jointly continuous in `u` and `(N, M)`,
being built from subtraction and matrix multiplication
(`continuous_step`). By induction on the number of steps, `strictParts w` is a
continuous function of the matrix `u` (`continuous_iterate_step`,
`continuous_strictParts`). Composing with the continuous maps
`g ↦ g.val.val` and `g ↦ (g.val⁻¹).val` (`Units.continuous_val`,
`Units.continuous_coe_inv`), the values `P, Q` and the inverses
`Q * g⁻¹, g⁻¹ * P` depend continuously on `g`. `Units.continuous_iff` turns
continuity of value and inverse into continuity into the unit group, and
`Continuous.subtype_mk` and `Continuous.prodMk` give continuity of
`factorMap`. These assemble into the homeomorphism `homeomorph n R w`, and
`homeomorph_apply_val` records that its underlying matrix-unit at `x` is
`x.1.val * x.2.val` by definition. The final theorem supplies
`homeomorph n K w` and this equation.

## Boundary cases and provenance

For `n = 0` every group is trivial; the step map is iterated zero times and
the same argument applies without special treatment. No assumption on `w` is
made: the identity permutation (all of `U` in the plus factor) and the
order-reversing permutation (all of `U` in the minus factor) are covered by
the same argument.

The factorization `U = U_w⁺ · U_w⁻` with uniqueness of expression is the
decomposition used by Shalika (1974) in the proof of Lemma 1.9, as recorded in
the paired Markdown of the statement. The argument here, including the step
map, the agreement bound and the explicit inverses, is internal matrix algebra
written for this proof; it is not attributed to a literature proof. The
module defines the public helper declarations named above; it changes no
existing Lean or Markdown pair, and asserts nothing about measures, Haar
measures, or representations.

## Complete unapplied declaration and axiom checks

The following file, importing this module, was compiled in the pinned
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings:

```lean
import Langlands.Group.GL.UpperUnipotentFactorizationProof

universe u

example :
    ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
      [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
      ∃ e : (Langlands.GeneralLinear.permutationUnipotentPlus n K w ×
          Langlands.GeneralLinear.permutationUnipotentMinus n K w) ≃ₜ
          Langlands.GeneralLinear.upperUnipotent n K,
        ∀ x : Langlands.GeneralLinear.permutationUnipotentPlus n K w ×
            Langlands.GeneralLinear.permutationUnipotentMinus n K w,
          (e x).val = x.1.val * x.2.val :=
  @Langlands.GeneralLinear.upperUnipotentFactorization

set_option pp.universes true in
#check @Langlands.GeneralLinear.upperUnipotentFactorization

#print axioms Langlands.GeneralLinear.upperUnipotentFactorization
```

The inspection outputs are:

```text
Langlands.GeneralLinear.upperUnipotentFactorization.{u_1} :
  Langlands.GeneralLinear.UpperUnipotentFactorizationStatement.{u_1}

'Langlands.GeneralLinear.upperUnipotentFactorization' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The Lean service also built the proof module with Lake and inspected the
unapplied declaration, reporting kind `theorem`, level parameters `["u"]` and
exactly these three axioms. These are development checks; independent semantic
review and formal exact-target validation remain separate acceptance
requirements.
