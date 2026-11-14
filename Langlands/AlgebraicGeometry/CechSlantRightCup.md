# Right-axis cup and shuffle slant

This is an internal extension of the ordered Čech cup, affine tensor section
comparison, and shuffle slant already defined in
[CechKunneth](CechKunneth.md) and [CechSlant](CechSlant.md). It introduces no
external theorem or new geometric hypothesis.

Let `P` be the fibre product of `X` and `Y` over `Spec R`, where `R` is any
commutative ring. The section algebra structures on `X` and `Y` are induced by
their structure maps. The index type of the cover `U` of `X` is finite, its
twofold intersections are affine, and every nonempty finite intersection of the
family `V` on `Y` is affine. There is no covering or cocycle condition on the
arbitrary input cochain `e`. The functional `l` is any `R`-linear functional on
the degree-one cochains for `U`; annihilation of coboundaries is not needed for
this chain-level identity.

`slant_mul_pull_right` proves that slant commutes with multiplication by an
arbitrary section pulled back from `Y`. Its proof chooses a preimage under the
affine tensor section equivalence. Tensor induction reduces to pure tensors,
where `slant_mul`, multiplicativity of section pullback, and commutation of
scalar multiplication with ring multiplication prove the formula. The additive
case follows from distributivity and additivity of slant.

`ev_cup_pull_right` then extracts the initial right-axis cup factor from an
arbitrary path evaluation. Restriction and section pullback preserve products,
and their compatibility with faces identifies the extracted factor as the
corresponding face of the cochain on `Y`.

`rightAxisCup U V y m` is the additive map on degree-`m` product-cover cochains
which cups on the left with the pullback of `y` from `Y`. If `y` is a degree-one
cocycle and `e` has degree `n+1`, `L_cup_pull_right` proves

\[
 L_{n+1}(p_2^*y\smile e)=-\,y\smile L_n(e).
\]

The proof separates the first shuffle term. Its initial `Y` edge is constant,
so the cocycle vanishes there. For the remaining terms, the three explicit
`step`/`degen` identities remove the first edge and reduce the path to the
shuffle indexed one lower on the remaining `Y` face. The evaluation formula,
compatibility of slant with restriction, and the alternating sign give the
negative of the cup product. The argument works in every characteristic.

This file proves only the raw right-axis formula. Descent to actual cohomology,
the left-axis relation, the full creation-contraction relation, and the host
exterior/coproduct comparison are not conclusions of this contribution.
