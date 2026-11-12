# Compact transport of simultaneous adelic height inequalities

This derived prerequisite works with actual number-field adelic group points and
actual algebraic matrix representations. It gives one comparison constant for a
finite family of representation-vector heights and transports the published
simultaneous minimum inequalities through a compact factor on the left.

The construction is motivated by Godement, *Domaines fondamentaux des groupes
arithmétiques*, Exposé 257 (1963; collected 1964), section 9.3, printed p.214
(PDF page 15). The rendered original page was read directly. In its first
paragraph, Godement writes `g = m p` with `m` in a fixed compact set and passes
from the minimum inequalities for `g` to such inequalities for `p` with a
uniformly enlarged constant. The Lean results implement this step for the
Library's number-field primitive-vector height. They do not use the printed
higher-rank line-weight comparison in Springer.

## Finite uniform comparison

`IsSimultaneousOrbitHeightDistortionBound F G r d ρ C B` means that, for each
`i < r`, each `k ∈ C`, every adelic point `g` and every nonzero rational vector
`v` in the representation `ρ i`, both inequalities hold:

```text
H_i(k g, v) ≤ B H_i(g, v),
H_i(g, v)   ≤ B H_i(k g, v).
```

The predicate is defined for an arbitrary real `B`; the existence theorem
returns a strictly positive bound. There is no norm-one restriction on the
points in these comparisons.

`exists_pos_simultaneous_orbitHeight_distortionBound` proves the predicate for
every compact `C`, provided each dimension `d i` is positive for `i < r`. Apply
the imported single-representation compact comparison to each `i : Fin r`,
obtaining positive bounds `b i`. The bound `B = 1 + ∑ i, b i` is positive and
dominates each `b i`; positivity of the primitive-vector height permits
enlarging both inequalities. This also covers `r = 0`.

## Minimum inequalities

The published `chainHeightMinimalSet` consists of norm-one points satisfying

```text
H_i(g, v_i) ≤ c H_i(g q, v_i)   for every i < r and q ∈ Q_i.
```

The subgroups `Q_i` are arbitrary rational subgroups here. Neither descent nor
line preservation is needed to transport inequalities already known to hold.

`IsSimultaneousOrbitHeightDistortionBound.chainHeightMinimalSet_transport`
uses a nonnegative distortion bound `B`, nonzero selected vectors, and a
nonnegative `c`. For any norm-one `k` in the comparison set, it proves both:

```text
g   in the minimum set at c  ⇒ k g in the minimum set at B² c,
k g in the minimum set at c  ⇒ g   in the minimum set at B² c.
```

For the first implication, compare `H_i(k g)` to `B H_i(g)`, apply the minimum
inequality, and compare `H_i(g q)` to `B H_i(k (g q))`. Associativity identifies
the last point with `(k g) q`. The second implication uses the two comparisons
in the reverse order. Multiplication preserves inequalities because `B` and
`c` are nonnegative. The squared constant accounts for the two comparisons.

`exists_pos_chainHeightMinimalSet_compact_transport` combines these results:
a compact set and a finite list of positive-dimensional representations
determine one positive constant `D`. Both implications then hold with `D c`,
uniformly in the norm-one points, the nonzero selected vectors, the rational
subgroups and every nonnegative `c`. A factor in the compact set must also lie
in the ambient norm-one subgroup for the minimum-set expressions to be typed.

## Scope

All statements retain arbitrary number fields and universe `u`. No
faithfulness, reductivity, affine embedding, nesting of rational subgroups or
closure of the compact set under inversion is assumed. The proof uses the
two-sided compact comparison from `AdelicOrbitHeightCompactBounds` and the
minimum-set definition from `AdelicHeightChain`.

This unit does not establish a uniform root bound or the chamber-reduction
statement. Adapted-line character comparisons, rank-one reduction, the
appropriate Levi restrictions and intrinsic torus coordinates remain further
obligations.
