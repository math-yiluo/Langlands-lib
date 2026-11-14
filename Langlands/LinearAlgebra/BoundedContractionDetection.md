# Joint contraction detection and alternation in a bounded family

This internal algebraic derivation extends `BoundedCreationContraction`.
It makes no claim that its relations or bounds have yet been constructed for
structure-sheaf cohomology.

Work over a commutative ring `R`, with modules `M n`, finitely many creator
and contraction directions `i`, and the relations

\[
 d_i c_j+c_jd_i=\delta_{ij}\operatorname{id}
\]

on every positive degree. Assume `M n` is zero above the number of directions.
`jointContraction d n` collects the maps `d i n` into a map from `M (n+1)`
to the family of all `M n` values.

`eq_zero_of_contractions_eq_zero` applies the earlier finite-set induction
`mem_of_contractions_mem` to the zero submodules and the set of all directions.
Both stability conditions hold by linearity, and the numerical condition
reduces to positivity of `n+1`. Therefore all positive-degree contractions
are jointly injective, as recorded by `jointContraction_injective`.

Let `v j` be chosen vectors of `M 1`. In addition suppose

\[
 c_j\bigl(d_i(v_j)\bigr)=\delta_{ij}v_j
\]

in degrees zero and one. The degree-one creation-contraction relation then
shows that every contraction kills `c j 1 (v j)`. Joint detection proves
`creator_square_eq_zero`.

Finally let `B : M 1 →ₗ[R] M 1 →ₗ[R] M 2` be a skew bilinear product,
with `c i 1 x = B (v i) x`, and assume the `v i` span `M 1`.
`cup_self_eq_zero` proves `B x x = 0` for every `x` by span induction:
the creator result handles the generators, skew symmetry cancels the
cross terms for sums, and bilinearity handles scalar multiples.
The argument uses no division and applies in characteristic two.

All of these results are conditional algebraic facts. Actual cohomological
creation-contraction relations, degree-zero formulas, the appropriate
cohomological bound, and the host exterior/coproduct comparison remain
separate obligations. The provenance is the previous internally derived
finite-set argument and elementary module operations, without an additional
literature theorem.
