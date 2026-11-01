# Finite equations for homomorphisms out of an integer-free ring

This is an internal algebraic construction supporting the integral-action step
of the Harris division-case representability argument. Its provenance is the
integer-basis reconstruction of linear maps, bilinearity of multiplication, and
the existing Mathlib ring-homomorphism API. It assumes no moduli or
representability theorem.

Let `O` and `R` be arbitrary unital rings, let `I` be a finite type, and let
`b : Basis I ℤ O`. Neither ring is assumed commutative. For a tuple `r : I → R`,
`Relations b r` consists of exactly the following equations, evaluated in the
full target ring:

\[
\sum_i b.\mathrm{repr}(1)(i)\,r_i=1,\qquad
\sum_k b.\mathrm{repr}(b_i b_j)(k)\,r_k=r_i r_j
\quad(i,j\in I).
\]

Integer multiplication in these formulas means the canonical integer scalar
action on the target additive group. There is one unit equation and one
multiplication equation for every ordered basis pair. `Solutions b R` is their
subtype in `I → R`. The empty basis and zero rings are allowed.

The linear map `b.constr ℤ r` evaluates an arbitrary `x` as the sum of its basis
coefficients times `r_i`. `relations_iff_constr` identifies the displayed
equations with preservation of the unit and multiplication on basis pairs.
`constr_map_mul` regards the two sides of multiplication preservation as
integer-bilinear maps and checks equality on both basis variables. Thus
`ofRelations b r h` is an actual unital ring homomorphism, with the stated
evaluation formula on every element and with value `r_i` on `b_i`.

Conversely, every unital ring homomorphism is integer-linear.
`constr_basis_values` identifies it with the reconstruction from its values on
the basis, and `relations_basis_values` proves the finite equations.
`equiv` gives the resulting equivalence between all ring homomorphisms `O →+* R`
and `Solutions b R`; both inverse laws are proved.

For every unital ring homomorphism `g : R →+* R'`, `Relations.map` transports the
equations by applying `g`. The function `map` applies `g` to each tuple entry.
`ofRelations_map`, `equiv_natural`, and `equiv_symm_natural` prove that the
reconstruction and equivalence commute with this arbitrary postcomposition.
No injectivity or flatness hypothesis is used.

These are equations for actual ring maps. They neither represent their solution
functor by a scheme nor construct an integral action lifting a given rational
action. They do not prove ambient moduli existence, polarization conditions,
smoothness, projectivity, or the host representability statement.
