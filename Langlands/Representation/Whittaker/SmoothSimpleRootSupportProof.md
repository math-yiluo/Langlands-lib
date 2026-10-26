# Uniform simple-root support for smooth Whittaker coefficients

`Langlands.Whittaker.smoothSimpleRootSupport.{uF,uV}` proves the unchanged
Library proposition
`Langlands.Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T r`.
It covers every prime, supplied p-adic field and topological data, and natural
rank parameter. The field universe and representation-carrier universe are
independent. The statement module and all its dependencies are imported without
modification.

Worker 657 implemented the Lean proof. Its mathematical route is the elementary
argument recorded by Workers 358 and 456 in the accepted statement's paired
Markdown; they are credited as coauthors for that argument. This is an internal
derived proof using published Library results. It does not invoke a torus
expansion or a gauge theorem, and makes no additional claim about the original
JPSS results discussed in the statement documentation.

For a coefficient `f`, `modelMap_surjective` supplies a vector `v` such that
`f(g) = ℓ(π(g)v)`. Let `K` be `Conductor.levelOpenSubgroup F.Carrier r 0`.
The published compactness theorem makes `K` compact, and
`Conductor.levelSubgroup_zero` identifies its underlying subgroup with the exact
integral subgroup in the target. Smoothness makes the orbit map locally
constant. Restricting this map to `K` and applying
`IsLocallyConstant.range_finite` proves that the actual orbit
`S = {π(κ)v : κ ∈ K}` is a finite set. No dimension bound on its linear span is
needed.

The private `adjacentUnipotent` is the actual upper-unipotent element
`u_i(t) = I + t E_(i,i+1)`, with inverse `u_i(-t)`. Its indices are precisely
`i.castSucc` and `i.succ`. The private helpers prove that it is continuous in
`t`, takes zero to the identity, has standard Whittaker character
`ψ.complex t`, and satisfies

```text
diagonalUnits a * u_i(t) = u_i(c*t) * diagonalUnits a,
c = a[i] / a[i+1].
```

For every `i : Fin r` and every vector `w` in the finite set `S`, local
constancy of the smooth orbit map and continuity of `u_i` make
`{t : π(u_i(t))w = w}` an open neighborhood of zero. Intersecting these finitely
many sets gives one open neighborhood. The Library theorem
`T.exists_additiveLattice_subset` supplies an integer `n` such that the full
lattice

```text
L_n = {t : T.discreteValuation t ≤ exp(n)} = ϖ^(-n) O
```

lies in that neighborhood. The private `exists_uniform_lattice` implements this
step. The integer `n` depends on the coefficient preimage and representation,
and is chosen before the diagonal tuple, integral factor, and root index.

Write `q = T.residueCardinality` and `N = T.additiveConductor ψ`. The theorem
chooses `R = q^(N-n)` at this point. The published residue-cardinality theorem
gives `q > 1`, so this integer power is strictly positive.

Now suppose `f(diagonalUnits a * κ)` is nonzero, and fix a root index. The
common lattice fixes `π(κ)v` under `u_i(t)` for every `t ∈ L_n`. The diagonal
identity and the defining equivariance of the actual Whittaker functional give

```text
f(diagonalUnits a * κ) = ψ.complex(c*t) * f(diagonalUnits a * κ).
```

Cancellation therefore gives `ψ(c*t) = 1`. The ratio `c` is nonzero because all
diagonal entries are units. Put `b = log(T.discreteValuation c)`. If
`x ∈ L_(b+n)`, multiplicativity of the valuation shows `x/c ∈ L_n`.
Consequently `ψ(x) = 1`, so `T.AdditiveTrivialAt ψ (b+n)` holds. Maximality of
the additive conductor, through `T.additiveTrivialAt_iff_le_conductor`, gives
`b+n ≤ N`. Finally the exact normalization is
`T.normalizedAbs c = q^b`; monotonicity of integer powers for `q > 1` gives
the requested bound `T.normalizedAbs c ≤ R`.

All topology and valuation instances in the proof come from the supplied `T`.
There is no topology on the representation carrier or continuity assumption on
the functional, and no irreducibility, admissibility, finite generation, or
central-character hypothesis. The same proof includes `r = 0`: the family of
root conditions is empty, and the final root-index quantifier is vacuous.
Zero functionals, coefficients, and representation spaces are also included;
the cancellation step is reached only under the target's nonvanishing premise.
The conclusion is exactly the uniform upper bound on adjacent root coordinates;
it adds no finite expansion or compact-support assertion.
