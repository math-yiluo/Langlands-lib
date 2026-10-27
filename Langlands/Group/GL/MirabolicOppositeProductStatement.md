# The actual opposite-parabolic–mirabolic product

Authors: Worker 452 (prepared draft), Worker 264.

`Langlands.GeneralLinear.MirabolicOppositeProductStatement.{u}` is a
proposition definition. It quantifies over every field `K : Type u`, every
`a b : ℕ` with `ha : 0 < a`, and every actual matrix
`g : GeneralLinear (a+b+1) K`. It uses the published binary shape
`MirabolicOppositeIntersection.shape a b ha`, whose ordered block sizes
are `a,b+1`.

Write `R` for that shape's actual lower, or opposite, parabolic subgroup,
and `P = GeneralLinear.mirabolic (a+b) K`. The proposition asserts

```text
(there exist r ∈ R and m ∈ P with g = r * m)
  ↔
(there exists j : Fin (b+1) with
   (g⁻¹) (Fin.last (a+b)) (Fin.natAdd a j) ≠ 0).
```

## Matrix values

By `BlockShape.mem_oppositeParabolic_iff` and the published binary
coordinates (`Fin.castAdd (b+1)` for the head, `Fin.natAdd a` for the
tail), an element of `R` is an invertible matrix whose entries in the head
rows `0,…,a-1` and tail columns `a,…,a+b` vanish. In block form it is
`[A,0;C,D]` with diagonal blocks of sizes `a` and `b+1`. An element of `P`
is an invertible matrix whose last row is `(0,…,0,1)`.

The factors are elements of these two published subgroups. The equality
compares their ambient values `r.val * m.val` with `g` in the unit group
`GeneralLinear (a+b+1) K`. The order is exactly the opposite-parabolic
factor followed by the mirabolic factor.

## Indices

`g⁻¹` is the inverse in the unit group. Its matrix is the inverse of the
matrix of `g` (Mathlib's `Matrix.coe_units_inv`). The row `Fin.last (a+b)`
is the last ambient coordinate `a+b`, counting from zero. The column
`Fin.natAdd a j` is the coordinate `a+j`. As `j` ranges over `Fin (b+1)`,
these are all `b+1` tail columns `a,…,a+b`, including the final column. The
right side therefore says that the tail part of the last row of `g⁻¹` is
not the zero vector.

## Boundary cases

The field universe is arbitrary. The case `b=0` is included. Then the tail
block has size one and, by `MirabolicOppositeIntersection.tail_last`, the
condition is `(g⁻¹) (Fin.last a) (Fin.last a) ≠ 0`. The hypothesis `a>0`
is the positivity required by the published binary shape. The proposition
says nothing about `a=0`. There are no topology, measure, representation,
nonzero-pivot or additional factorization hypotheses.

## Provenance

This is derived internal infrastructure, not a transcription of a
literature theorem. It is an internal algebraic statement about the actual
matrix groups in `Mirabolic` and `OppositeBlocks`, through their published
binary specialization in `MirabolicOppositeIntersection`. It is stated as
an algebraic prerequisite of the normalized square-integrable block
induction irreducibility task.

The elementary motivation is as follows. If `g=r*m`, then the mirabolic
equation for `m⁻¹` makes the last row of `g⁻¹` equal to the last row of
`r⁻¹`. Its tail is the last row of the invertible tail diagonal block of
`r⁻¹`, so it is nonzero. Conversely, write the last row of `g⁻¹` as `(x,y)`
with head part `x` and tail part `y≠0`. Extend `y` to the last row of an
invertible tail matrix `D`. A lower block matrix `q=[I,0;C,D]` then has last
row `(x,y)` when the last row of `C` is chosen to be `x`. The product `q*g`
has the mirabolic last row. Taking `r=q⁻¹` and `m=q*g` gives the required
factors.

This explanation is a proposed proof route. The module defines only the
proposition and proves neither direction. It asserts no continuous or
measurable selection of factors, no openness or conullity of the product,
no quotient-measure conclusion, and no induction or irreducibility result.
