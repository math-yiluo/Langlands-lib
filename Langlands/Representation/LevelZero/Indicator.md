# Functions supported on the inducing subgroup, and coinvariants killed by finite sums

Lean module: `Langlands.Representation.LevelZero.Indicator`, namespace `Langlands.LevelZero`.

## Indicator functions in smooth induction

Let `G` be a topological group, `J` a subgroup and `Λ : Representation ℂ J V`. The smooth
induced representation `Induction.smoothInduced J Λ` acts by right translation on the smooth
functions `f : G → V` with `f (j * x) = Λ j (f x)`.

- `indicatorFun J Λ v` is the function equal to `Λ j v` at `j ∈ J` and to `0` off `J`. It is
  covariant (`indicatorFun_cov`), additive and homogeneous in `v`, and
  `indicatorFun_mul_mem` gives `indicatorFun J Λ v (x * j) = indicatorFun J Λ (Λ j v) x` for
  `j ∈ J`.
- If `S` is an open subgroup with `S ≤ J` on which `Λ` is trivial, `indicatorFun J Λ v` is
  invariant under right translation by `S` (`indicatorFun_mul_open`). `indicator J Λ S hSJ hΛS v`
  is the resulting smooth induced function, and `indicatorLinear` the linear map `v ↦` it.
- `smoothInduced_indicator`: translation by `j ∈ J` sends the function of `v` to the function
  of `Λ j v`. `indicator_one_eval`: the value at `1` is `v`.
- `Induction.eval_smoothInduced`, `eval_add`, `eval_smul`, `eval_zero`, `eval_cov`, `ext_eval` are the
  evaluation rules of smooth induced functions.

## Coinvariants

For a complex representation `ρ` of a group and a subgroup `N`, `Jacquet.relations ρ N` is the
span of the vectors `ρ n w - w` and `Jacquet.Coinvariants ρ N` the quotient by it.

- `mem_relations_of_sum_eq_zero`: if a nonempty finite family `n i` in `N` satisfies
  `∑ i, ρ (n i) w = 0`, then `w` lies in the relations, since
  `card • w = ∑ i, (w - ρ (n i) w)` and the cardinality is invertible in `ℂ`.
- `coinvariants_subsingleton_of_span`: the coinvariants vanish when a spanning set lies in the
  relations.

Vanishing also passes to the target of a surjective intertwiner by `Langlands.CuspidalSupport.QuasicuspidalEmbedding.coinvariants_subsingleton_of_surjective`. [Quasicuspidal embedding](../CuspidalSupport/QuasicuspidalEmbeddingProof.md)

Provenance: internal; elementary facts about induced representations and Jacquet coinvariants.
