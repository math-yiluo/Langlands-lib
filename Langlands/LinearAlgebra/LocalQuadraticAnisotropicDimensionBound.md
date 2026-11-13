# The anisotropic quadratic dimension bound over nonarchimedean local fields: proof

The theorem `Langlands.localQuadraticAnisotropicDimensionBound` proves the
published proposition `Langlands.LocalQuadraticAnisotropicDimensionBoundStatement`
at arbitrary universe levels `u` and `v`. Let `K` be a nonarchimedean local field
and `V` a finite-dimensional `K`-vector space. Every anisotropic `QuadraticForm K V`
then has `Module.finrank K V ≤ 4`. No step assumes a characteristic of `K` or of
its residue field, so characteristic two is included. No step assumes a
nondegenerate polar form either, so singular forms are covered.

Throughout, `v` means `ValuativeRel.valuation K`, which takes values in
`ValueGroupWithZero K`. The integers are `𝒪[K]`, the maximal ideal is `𝓂[K]` and
the residue field is `𝓀[K]`. The auxiliary results live in the namespace
`Langlands.LocalQuadraticAnisotropic`.

## Relation to the literature

Petersson (2013, §§2.1–2.5, formula (13)) bounds the dimension by attaching two
anisotropic residue forms over the finite residue field to an anisotropic form.
The implemented proof uses the same idea but avoids lattices and their
filtrations. It builds a "dominant" family of vectors, a valuation-orthogonal
basis. It scales the family so that every value is `1` or `v ϖ`. Each of these
two value classes then gives an anisotropic quadratic form over `𝓀[K]`. The
published finite-field bound `Langlands.QuadraticPolynomial.finiteField_finrank_le_two`
shows that each class has at most two members. All intermediate results below
are proved in this module. The only imported project results are the target
statement and the coordinate-polynomial module
`Langlands.LinearAlgebra.QuadraticFormCoordinatePolynomial`.

## Step 1: Hensel's lemma (`exists_root_sq_add_self_add`)

If `v t < 1`, then `u ^ 2 + u + t` has a root `u` in `K`. Mathlib makes `𝒪[K]`
`𝓂[K]`-adically complete, and therefore Henselian, once `K` carries the uniform
structure of its additive topological group. The proof chooses that uniform
structure. The monic polynomial `X ^ 2 + X + t` over `𝒪[K]` has the root `0`
modulo `𝓂[K]`, where its derivative `1` is a unit. `HenselianRing.is_henselian`
lifts this to a root. The lemma `valuation_two_le_one` records that `v 2 ≤ 1`.

## Step 2: the polar bound and the ultrametric inequality

`polar_sq_le` proves `v (polar Q x y) ^ 2 ≤ v (Q x) * v (Q y)` for anisotropic
`Q`, by contradiction. Write `b = polar Q x y`. If the inequality fails, then
`b ≠ 0`, so `x ≠ 0` and `Q x ≠ 0`. The element `t = Q x * Q y / b ^ 2` then has
`v t < 1`. Step 1 gives a root `u` of `u ^ 2 + u + t`. Put `s = b / Q x * u`;
expanding gives

`Q (s • x + y) = (b ^ 2 / Q x) * (u ^ 2 + u + t) = 0`.

Anisotropy forces `y = -(s • x)`, so `Q y = s * s * Q x` and
`b = -(s * (2 * Q x))`. Hence `b ^ 2 = 4 * (Q x * Q y)`. Because `v 4 ≤ 1`, this
gives `v b ^ 2 ≤ v (Q x) * v (Q y)`, a contradiction. The argument is uniform in
the characteristic: in characteristic two the identity reads `b = 0`, which
contradicts `b ≠ 0` directly.

From this bound, `val_polar_le_max` gives `v (polar Q x y) ≤ max (v (Q x)) (v (Q y))`.
Then `val_map_add_le` derives the ultrametric inequality
`v (Q (x + y)) ≤ max (v (Q x)) (v (Q y))` from
`Q (x + y) = Q x + Q y + polar Q x y`. The variants `val_map_sub_le` and
`val_map_sum_le`, for differences and finite sums, follow.

## Step 3: dominant families

A family `e : ι → V` is `Dominant Q e` when every term of every linear
combination is dominated by the whole combination:
`v (Q (a i • e i)) ≤ v (Q (∑ j, a j • e j))` for all coefficients `a` and all
indices `i`.

`exists_min` shows that best approximation from the span of a dominant family
`e : Fin k → V` of nonzero vectors exists. For every `x` there are coefficients
`a₀` minimizing `F a = v (Q (x - ∑ j, a j • e j))`. The coordinate polynomial
from `QuadraticFormCoordinatePolynomial`, evaluated at `Fin.cons 1 (-a)`,
computes `Q (x - ∑ j, a j • e j)`. So `F` is continuous, by the continuity of
polynomial evaluation and of the valuation for the valuative topology. On the
box of coefficients with `v (a j) ≤ max 1 (v (Q x) / v (Q (e j)))`, which is
compact because closed balls of a local field are compact, `F` attains a
minimum at some `a₀`.

Outside the box, some coordinate has `v (a j) > 1` and
`v (a j) * v (Q (e j)) > v (Q x)`. This gives
`v (Q (a j • e j)) = v (a j) ^ 2 * v (Q (e j)) > v (Q x)`. Dominance and the
ultrametric inequality then give `F a ≥ v (Q (∑ i, a i • e i)) > v (Q x) = F 0 ≥ F a₀`.
So `a₀` is a global minimizer.

`dominant_snoc` shows that appending the best-approximation error
`y = x - ∑ j, a₀ j • e j` keeps the family dominant. Consider a combination
`w + t • y`, where `w` is a combination of the old vectors. If `t ≠ 0`, then
`w + t • y = t • (x - ∑ j, (a₀ j - t⁻¹ * b j) • e j)`. Minimality of `a₀` then
gives `v (Q (t • y)) ≤ v (Q (w + t • y))`. The old terms are dominated by `w`.
In turn, `w` is dominated through the ultrametric inequality applied to
`w = (w + t • y) - t • y`.

`exists_dominant` builds, by induction, a dominant family of nonzero vectors of
every length `k ≤ finrank K V`. While `k < finrank K V`, the span of the family
is not everything (`finrank_range_le_card`). So some `x` lies outside the span,
and its best-approximation error is nonzero and can be appended.

## Step 4: normalizing values (`exists_normalizer`)

The unit group of `ValueGroupWithZero K` is cyclic. Choose a generator `g` and
`ϖ` with `v ϖ = g`. Every nonzero value is `g ^ k`. Choosing `c` with
`v c = g ^ (-(k / 2))` gives `v c * v c * g ^ k ∈ {1, v ϖ}`, according to the
parity of `k`. Scaling each vector of a dominant family by such a `c` keeps it
dominant, and every value becomes `1` or `v ϖ`.

## Step 5: the residue lemma (`card_le_two_of_residue`)

Let `q` be a quadratic form on `ι → K` with `ι` finite, and let `c ≠ 0`.
Suppose that `v (q a) ≤ v c` for every integral vector `a`, and that
`v (q a) = v c` whenever some coordinate of such an `a` is a unit. Then
`Fintype.card ι ≤ 2`.

The proof chooses a linear order on `ι`. It uses Mathlib's triangular bilinear
form `QuadraticMap.toBilin` for the standard basis. The entries `T i j` of that
form are `q (Pi.single i 1)` on the diagonal, polar values above it and `0`
below it, and they satisfy `q a = ∑ i, ∑ j, a i * (a j * T i j)`. The hypothesis
applied to basis vectors and to sums of two basis vectors shows that every
`c⁻¹ * T i j` is integral. Reducing that matrix to `𝓀[K]` defines a quadratic
form `q̄` over the residue field.

`q̄` is anisotropic. Lift a nonzero zero `ā` of `q̄` to an integral vector `a`;
some coordinate of `a` is a unit. Then `c⁻¹ * q a` has valuation `1`, so it is a
unit, but its residue is `q̄ ā = 0`. The residue field is finite, and
`finiteField_finrank_le_two` bounds `card ι` by two. This argument also allows
characteristic two and singular `q̄`.

## Step 6: the main theorem

`localQuadraticAnisotropicDimensionBound` takes a dominant family `e` of
`n = finrank K V` nonzero vectors (Step 3). It rescales the family to a dominant
family `f` with every `v (Q (f i))` equal to `1` or `v ϖ` (Step 4). For a class
`s` of indices with common value `v d`, it applies Step 5 to the form
`a ↦ Q (∑ i ∈ s, a i • f i)`, built with `Fintype.linearCombination`. The upper
bound follows from `val_map_sum_le`. For the lower bound, extend the
coefficients by zero outside `s` and apply dominance of `f` at an index whose
coefficient is a unit. This gives `v (Q (∑ i ∈ s, a i • f i)) ≥ v d`. So each of
the two classes has at most two elements. Every index lies in one of them, so
`n ≤ 2 + 2 = 4`.
