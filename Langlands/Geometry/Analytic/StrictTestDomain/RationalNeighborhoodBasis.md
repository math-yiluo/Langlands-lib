# Strict rational neighbourhood bases of spectrum points

Author: Worker 1010.

Fix a complete normed field K with ultrametric absolute value and a presented
strict affinoid algebra P over K. Write `M(P)` for its Banach spectrum. Rational
data are the published `StrictTestDomain.RationalData K P`: a denominator g and
numerators `fⱼ` with no common zero on `M(P)`. Their locus is the set of points
x with `x fⱼ ≤ x g` for all j.

## Finite intersections

`RationalData.listInter` turns a finite list of rational data into one rational
datum. The empty list gives the published whole-spectrum datum `whole K P`. A
list `d :: l` gives the published intersection `d.inter (listInter l)`.
`mem_locus_listInter` states that a point lies in the resulting locus exactly
when it lies in the locus of every member of the list. The proof is induction
on the list, using the published `locus_whole` and `locus_inter`.

## Replacing real thresholds by unit radii

Fix c in K with `‖c‖ > 1`. Points of `M(P)` restrict to the norm on K
(published `BanachSpectrum.algebraMap_apply`). So a monomial
`f = c^(-m) aⁿ`, with m an integer and n a natural number, has value
`x f = ‖c‖^(-m) (x a)ⁿ` at every point x.

- `exists_upper_unit_bound`: let `x a < r` with `r > 0`. Then some f in P
  satisfies `x f < 1`, and every point y with `y f ≤ 1` satisfies `y a ≤ r`.
- `exists_lower_unit_bound`: let `q < x b` with `q > 0`. Then some f in P
  satisfies `1 < x f`, and every point y with `1 ≤ y f` satisfies `q ≤ y b`.

Both proofs take `f = c^(-m) aⁿ`, respectively `c^(-m) bⁿ`.

For the upper bound, first choose n with `((x a)/r)ⁿ < ‖c‖⁻¹`. Then choose m
with `‖c‖^m ≤ rⁿ < ‖c‖^(m+1)` (Mathlib's `exists_mem_Ico_zpow`). Hence
`(x a)ⁿ < rⁿ/‖c‖ < ‖c‖^m`, which gives `x f < 1`. If `y f ≤ 1`, then
`(y a)ⁿ ≤ ‖c‖^m ≤ rⁿ`, and so `y a ≤ r`.

For the lower bound, choose n with `(q/(x b))ⁿ < ‖c‖⁻¹`, and m′ with
`‖c‖^m′ ≤ qⁿ < ‖c‖^(m′+1)`. Take `m = m′ + 1`. Then
`qⁿ < ‖c‖^m ≤ ‖c‖ qⁿ < (x b)ⁿ`, which gives `x f > 1`. If `1 ≤ y f`, then
`qⁿ < ‖c‖^m ≤ (y b)ⁿ`, and so `q ≤ y b`.

## The neighbourhood basis

`RationalData.exists_locus_mem_nhds_subset` assumes that K has an element of
norm greater than one. For every point x and every neighbourhood V of x, it
gives rational data d whose locus is a neighbourhood of x contained in V.

The proof starts from the published
`BanachSpectrum.exists_finite_laurent_neighborhood`. It gives finitely many
elements `aᵢ` and `bⱼ` with positive real thresholds, satisfying
`x aᵢ < rᵢ` and `qⱼ < x bⱼ`, such that the locus of `y aᵢ ≤ rᵢ` and
`qⱼ ≤ y bⱼ` lies in V.

Apply the two lemmas above to each threshold. This gives elements `fᵢ` and
`gⱼ`. Then d is the list intersection of the published binary Laurent data
`laurentUpper fᵢ` (locus `y fᵢ ≤ 1`) and `laurentLower gⱼ` (locus `1 ≤ y gⱼ`).

- Its locus lies in the Laurent locus above, and hence in V.
- It is a finite intersection of closed half-spaces of continuous evaluation
  maps. At x each of these inequalities is strict. So the locus is a
  neighbourhood of x.
