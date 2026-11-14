# A separating coordinate for a finite-index enlargement of integral points

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. Its two definitions are
auxiliary predicates. Everything here is derived; nothing is quoted from a source.

## Value predicates

For a local ring `R` and an `R`-algebra `K`:

- `IsIntUnit R z` means `z = algebraMap R K r` for a unit `r` of `R`;
- `IsIntSmall R z` means `z = algebraMap R K r` for some `r` in the maximal ideal of `R`.

The `ValueLemmas` section proves the elementary facts used later:

- both predicates imply integrality (`mem_range`);
- an integral non-unit value is small (`isIntSmall_of_not_isIntUnit`);
- when `K` is a fraction field of `R`, a unit value is not small (`not_isIntSmall_of_isIntUnit`);
- products of unit values are unit values (`IsIntUnit.mul`, `IsIntUnit.pow`);
- if a product of two integral values is a unit value, so is each factor
  (`IsIntUnit.of_mul_left/right`);
- a small value times an integral value is small (`IsIntSmall.mul`, `mul_left`).

For a discrete valuation ring with uniformiser `ϖ`:

- `isIntSmall_mul_pow`: if `ϖ ^ N g` is integral and `f` is small, then `g f ^ (N + 1)` is small;
- `isIntUnit_of_not_mem`: if `ϖ ^ (m + 1) z` is integral but `ϖ ^ m z` is not, then
  `ϖ ^ (m + 1) z` is a unit value;
- `isIntSmall_pow_succ_mul`: `ϖ ^ (m + 1) z` is small whenever `z` is integral.

`ev_mul_apply`, `ev_pow_apply` and `ev_one_right` record that each `ev x` is a ring map.

## Cosets

For subgroups `U, V` of a group `P`:

- `exists_finset_of_finiteIndex`: if `U.subgroupOf V` has finite index, there is a finite set
  `T` such that every `x ∈ V` is `r * u` with `r ∈ T` and `u ∈ U` (the representatives
  `Quotient.out` of the finitely many cosets);
- `exists_pow_succ_mem`: if `U.subgroupOf V` is normal of finite index, there is `n` with
  `x ^ (n + 1) ∈ U` for every `x ∈ V` (take `n + 1` the index, by `Subgroup.pow_index_mem`);
- `inv_mul_mul_mem`: if `U ≤ V` and `U.subgroupOf V` is normal, then `x⁻¹ u x ∈ U` for
  `x ∈ V`, `u ∈ U`.

## The separating coordinate

Work in the setting of module `Translation`: `R` is a Henselian discrete valuation ring with
algebraically closed residue field and fraction field `K`; `A` is a smooth commutative Hopf
algebra over `R`; `ev : P →* WithConv (A →ₐ[R] K)`; `U` satisfies `hU` and `hsurj`. Let `V ⊇ U`
with conjugation hypothesis `hnorm`, a finite set of coset representatives `T` as above, and
`hpow : x ^ (n + 1) ∈ U` for `x ∈ V`.

`exists_bound`: for a uniformiser `ϖ` and `a : A` there is `N` with `ϖ ^ N ev x a ∈ R` for all
`x ∈ V`. Take the maximum over the finitely many representatives in `T` of the bounds from
`exists_pow_smul_mem`.

`exists_separating` (main result): there is `e : A` that is integral on `V`, has
`IsIntUnit R (ev 1 e)`, and has `IsIntSmall R (ev x e)` for every `x ∈ V \ U`.

It is the case `W = V` of `exists_separating_aux`. That lemma proves the same statement for
every intermediate subgroup `U ≤ W ≤ V`, by strong induction on the number of elements of `T`
lying in `W`. For a fixed `W`:

1. Let `S f` mean that `f` is integral on `W` and `ev 1 f` is a unit value. Let `supp f` be the
   set of representatives `r ∈ T ∩ W` such that `f` takes a unit value somewhere on `r U`.
   Choose `f₀` with `S f₀` and `supp f₀` of minimal cardinality (`1` satisfies `S`).
2. Every `g` with `S g` takes a unit value on each coset `x U` (`x ∈ W`) on which `f₀` does.
   Indeed `S (f₀ g)` holds, and by `IsIntUnit.of_mul_left/right` we have
   `supp (f₀ g) ⊆ supp f₀ ∩ supp g`. Minimality forces `supp (f₀ g) = supp f₀`, so
   `supp f₀ ⊆ supp g`. `exists_isIntUnit_iff` lets one test a coset at its representative.
3. Let `H` be the set of `x ∈ W` such that `f₀` takes a unit value on `x U`. It contains `U`.
   It is closed under products: if `f₀ (x u₀)` is a unit value, the translation lemma
   `exists_left_translate` gives `g` with `ev y g = ev (x u₀ y) f₀`, which satisfies `S g`.
   Step 2 applied to `g` at `y` then gives a unit value of `f₀` on `x y U`, after rewriting with
   the conjugation hypothesis. It is closed under inverses because
   `x⁻¹ = x ^ n (x ^ (n + 1))⁻¹` with `x ^ (n + 1) ∈ U`. So `H` is a subgroup with
   `U ≤ H ≤ W`.
4. If `H = W` and `W = U`, then `e = f₀` works (the smallness condition is vacuous).
5. If `H = W` but some `v ∈ W` is not in `U`, we derive a contradiction. By `hU` some `a` has
   `ev v a ∉ R`. Let `m` be minimal with `ϖ ^ m a` integral on `W`; it exists by `exists_bound`
   and is positive. At a point `x₁ ∈ W` where `ϖ ^ (m - 1) a` is not integral, `ϖ ^ m a` takes a
   unit value (`isIntUnit_of_not_mem`). The left translate `g` of `ϖ ^ m a` by `x₁` satisfies
   `S g`. Since `x₁⁻¹ ∈ H`, step 2 gives `u ∈ U` with `ϖ ^ m ev u a` a unit value. But
   `ev u a ∈ R`, so this value is small (`isIntSmall_pow_succ_mul`), a contradiction.
6. If `H ≠ W`, some representative in `T ∩ W` is not in `H`, so the induction hypothesis
   applies to `H` and gives `g`. Let `N` be a bound for `g` on `V` (`exists_bound`) and put
   `e = g f₀ ^ (N + 1)`.
   - On `W \ H`, `f₀` is integral but not a unit value, hence small, so `e` is small there
     (`isIntSmall_mul_pow`).
   - On `H`, `g` is integral, and it is small off `U`.
   - At `1`, both factors are unit values.

## Provenance

This construction replaces the scheme-theoretic argument of Kaletha–Prasad Proposition A.7.1
by an elementary argument on coordinate values. It was devised for this formalization and is
not a transcription of a published proof.
