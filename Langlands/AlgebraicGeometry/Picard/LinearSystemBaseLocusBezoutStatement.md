# A Bezout count for a section against a linear system with finite base locus

`LinearSystemBaseLocusBezoutStatement` is a numerical intersection bound for one
section of a line-bundle power against a linear system of another power. It is
stated with the published actual Euler polynomial.

## Statement

The proposition quantifies over a universe `u`, an infinite field `K : Type u`,
and an integral, Noetherian, separated scheme `X` with a proper morphism
`f : X ⟶ Spec K`. It also quantifies over a natural number `e` with `0 < e` and
`topologicalKrullDim X ≤ e`, an actual line bundle `L`, natural numbers `p` and
`q`, a global section `s : L.powSections p` of the actual `p`th tensor power,
and an arbitrary set `S` of global sections of the actual `q`th tensor power.

For a section `t`, `L.sectionOpen t` is the published generation open
(`trivializationOpen` in `Ample.lean`): the points where `t` generates the
stalk. So `x ∉ L.sectionOpen t` says that `t` vanishes at `x`. The *base locus*
`B` of `S` is the set of points `x` with `∀ t ∈ S, x ∉ L.sectionOpen t`, the
points where every member of `S` vanishes. It is closed.

The proposition has three explicit hypotheses:

1. the generation open of `s` is nonempty, so `s` is not identically zero;
2. the base locus `B` is a finite set;
3. at every point of `B` where `s` also vanishes, the stalk
   `X.presheaf.stalk x` has ring Krull dimension exactly `e`.

Under these hypotheses it asserts the rational inequality

`Nat.card {x // (∀ t ∈ S, x ∉ L.sectionOpen t) ∧ x ∉ L.sectionOpen s}
   ≤ e! * p * q ^ (e - 1) * coeff e (lineBundleEulerPolynomial f L e)`.

The counted points form a subset of `B`, so by hypothesis 2 there are finitely
many of them, and `Nat.card` is their number. The polynomial
`lineBundleEulerPolynomial f L e` is the published Newton polynomial, truncated
at degree `e`, of the actual Euler characteristics `m ↦ χ(L^m)`. Under
`topologicalKrullDim X ≤ e` it evaluates to them at every natural number
(`lineBundleEulerPolynomial_eval`). When `dim X = e`, Stacks Definition 33.45.3
with all `L_i = L` defines `(L^e · X)` as the coefficient of `n_1 ⋯ n_e` in
`χ(L^(n_1 + ⋯ + n_e))`. That coefficient is `e!` times the degree-`e`
coefficient above, so the right side is `p * q ^ (e - 1) * (L^e · X)`.

## The hypotheses

- **`IsIntegral X`.** Every nonzero section of a line bundle on `X` is then a
  nonzerodivisor, so the cut by `s` is injective. `Γ(X, O_X)` is a field, which
  settles the degenerate cases below.
- **`[IsNoetherian X]` and `[X.IsSeparated]`.** Both already follow from
  properness over a field. They are instance arguments only so that the
  statement matches the published API `lineBundleEulerPolynomial_eval`.
- **`[Infinite K]`.** Over an infinite field, a finite union of proper
  subspaces of the `K`-span of `S` is never the whole span. This lets the proof
  choose generic members of the span that avoid finitely many prescribed points
  outside `B`. The bound is not claimed to need it: over a finite field one could
  argue one component at a time instead. In the intended application `K` is
  algebraically closed, so it is infinite.
- **`0 < e`.** This excludes the zero-dimensional case. There the exponent
  `e - 1` would be `0` under natural subtraction, and the count is zero anyway:
  `X` is one point, and `s`, being a nonzero section of a line bundle over a
  field, vanishes nowhere.
- **Hypothesis 1 (`s` is not identically zero).** Without it the bound fails.
  On `X = ℙ¹_ℚ`, take `e = 1`, `L = O(1)`, `p = 0`, `s = 0`, `q = 1` and
  `S = {x₀}`. The count is `1`, since `s` vanishes at the single point of `B`,
  whose local ring has dimension `1`. The right side is `0` because `p = 0`.
- **Hypothesis 2 (finite base locus).** This is the defining hypothesis of the
  classical bound. It makes the counted set finite, so `Nat.card` is a genuine
  count; for an infinite type `Nat.card` would be `0`. It also drives the proof:
  each point outside `B` lies off the zero locus of some member of `S`, so
  generic members of the span cut every positive-dimensional piece properly.
  The statement makes no claim when the base locus is infinite (excess
  intersection). In the intended application `B` is the finite set of
  `n`-torsion points.
- **Hypothesis 3 (local dimension `e` at the counted points).** Without it the
  bound fails once `dim X < e`. On `X = ℙ¹_ℚ`, take `e = 2`, `L = O(1)`,
  `p = q = 1` and `s = x₀`, `S = {x₀}`. Then `B` is one point and the count is
  `1`. But `χ(O(m)) = m + 1` has degree-`2` coefficient `0`, so the right side is
  `0`. The point's local ring has dimension `1`, so hypothesis 3 rules this out.
  When `dim X = e` hypothesis 3 is automatic. `X` is of finite type over `K`, so
  points of the finite closed set `B` are closed, and at a closed point of an
  integral scheme of finite type over a field the local ring has dimension
  `dim X`. The premise is kept so that the statement does not depend on that
  piece of dimension theory, and so that it covers `dim X < e` correctly.
- `S` is a set of sections, not a subspace. Its base locus equals that of the
  `K`-span of `S`. Nothing is assumed about ampleness or global generation of
  `L`, or about the sign of the coefficient.

## Degenerate cases

- **`p = 0`.** The `0`th power is the structure sheaf and `Γ(X, O_X)` is a
  field, because `X` is integral and proper over `K`. By hypothesis 1, `s` is
  nonzero, so it is a unit and vanishes nowhere. The count is `0`, and the
  right side is `0` because of the factor `p`.
- **`q = 0`.** Every `t ∈ S` lies in the field `Γ(X, O_X)`.
  - If some `t ∈ S` is nonzero, it vanishes nowhere, so `B` is empty and the
    count is `0`. For `e ≥ 2` the right side is `0` because `0 ^ (e - 1) = 0`.
    For `e = 1` it is `p` times the degree-`1` coefficient. That coefficient is
    `0` if `dim X = 0`. If `dim X = 1` it equals `deg L`, which is `≥ 0` when
    `p ≥ 1`, because `L ^ p` has the nonzero section `s`.
  - If every member of `S` is zero, or `S` is empty, then `B = X`. Hypothesis 2
    makes `X` finite. An integral scheme of finite type over a field with
    finitely many points is a single point, of dimension `0 < e`. Hypothesis 3
    then makes the count `0`, and the degree-`e` coefficient is `0`.
- **`dim X < e`.** Each local ring has dimension at most `dim X < e`, so
  hypothesis 3 makes the counted set empty. The function `m ↦ χ(L^m)` is a
  polynomial of degree at most `dim X` (Stacks Lemma 33.45.1), so its Newton
  polynomial truncated at `e` has degree-`e` coefficient `0`. Both sides are
  `0`. So the bound has content only when `dim X = e`.

## Provenance and role

This is derived content: the classical Bezout bound for a section and a linear
system, in the cohomological form of The Stacks Project, Section 33.45
Numerical intersections (tag 0BEL), source
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`. It rests on
Lemma 33.45.1 (degree bound for Euler polynomials of coherent sheaves),
Lemma 33.45.2 (the leading coefficient depends only on the lengths at the
generic points of top-dimensional components), Definition 33.45.3
(intersection numbers as Euler coefficients) and Lemma 33.45.8 (cutting by an
effective Cartier divisor). The displayed bound is not a single numbered result
there. It combines these with the fact that a module of positive dimension at a
point keeps that point in its support after one cut. The Euler characteristic
of a sheaf with finite support, used in step 4 of the route below and in the
remark after it, is Stacks Lemma 33.33.3 (Section 33.33 Euler
characteristics, tag 0BEI, source
`stacks-euler-characteristics-0BEI-2026-11-01`).

The statement serves the proof of
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(task `a76410a4-bece-4011-b3f8-7d87460be52c`). That target follows Mumford,
Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd edition (1994), proof of
Proposition 7.7, printed pp.138-139 (source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).
That proof bounds the number of `n`-torsion points on a hyperplane by an
intersection number. In the application `K` is algebraically closed, `e = g`,
`p = 1`, `q = n ^ 2` and `L` is the actual cubic bundle. The section `s` is a
nonzero linear form pulled back along the embedding. `S` is the set of
pulled-back linear forms through the origin, transported along
`[n]^* M ≅ M^(n*n)`.

## Intended proof route

The statement records no proof. One route, in coherent sheaves:

1. Cut `O_X` by `s`, which is injective since `X` is integral. The published
   `SectionCokernelEulerCoefficientStatement` gives the cokernel's degree
   `e - 1` coefficient as `e * p` times the degree-`e` coefficient of `L`.
2. Repeat `e - 1` times, starting from the current coherent sheaf `M` of
   dimension `d ≥ 1`. First pass to the quotient `M'` of `M` by its subsheaf
   of sections supported in `B`. This subsheaf has finite support, so the
   quotient changes the Euler polynomial by a constant. It keeps its top
   coefficient and keeps every point where `M` has positive local dimension.
   The associated points of `M'` lie outside `B`. They are finitely many, so a
   generic member `t` of the `K`-span of `S` avoids them all and is injective
   on `M'`. The cokernel of `t` has dimension at most `d - 1`, and its degree
   `d - 1` coefficient is `d * q` times the degree-`d` coefficient of `M'`. A
   similar quotient, which removes embedded associated points, appears in the
   proof of Stacks Lemma 33.45.1.
3. By Krull's principal ideal theorem (Mathlib's
   `supportDim_le_supportDim_quotSMulTop_succ`), each cut lowers the local
   dimension at a counted point by at most one. Each counted point starts with
   local dimension `e - 1` after the first cut, by hypothesis 3. So it stays in
   the support of the final sheaf.
4. The final sheaf has finite support. Its Euler characteristic is the
   `K`-dimension of its global sections, which is at least the number of points
   in its support, hence at least the count. By steps 1 and 2 it equals
   `e! * p * q ^ (e - 1)` times the degree-`e` coefficient.

The quotient in step 2 is needed. Without it a cut can have a nonzero kernel
supported in `B`, coming from embedded points. The kernel's Euler
characteristic then adds to the final Euler characteristic, which can exceed
the right side, and the comparison breaks. The kernel has finite support, so by
Stacks Lemma 33.33.3 its global sections are the direct sum of its stalks and
its Euler characteristic is their `K`-dimension. A composition series of each
stalk turns this into the sum over its support points `x` of `[κ(x) : K]` times
the length of the stalk at `x`. When `K` is not algebraically closed this
weighted sum can differ from the plain length.
`CoherentIntegralIdealFiltrationStatement` (filtrations with integral pieces)
is another way to organize the choice of generic members.
