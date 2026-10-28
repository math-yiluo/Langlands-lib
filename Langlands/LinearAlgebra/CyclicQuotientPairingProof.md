# A balanced nondegenerate pairing on a cyclic polynomial quotient

`Langlands.cyclicQuotientPairing.{uK}` proves exactly the published proposition
`Langlands.CyclicQuotientPairingStatement.{uK}`. For every field `K : Type uK`
and every nonzero polynomial `q`, it supplies a `K`-valued bilinear form on
`AdjoinRoot q` that is symmetric, nondegenerate on both sides, and balanced
under multiplication by every quotient element. No characteristic, monicity,
irreducibility, separability, or positive-degree assumption is added.

## Implemented proof

The private helper `cyclicQuotientPairing_monic` first treats monic `q`. Write
`d = q.natDegree`. Mathlib's `AdjoinRoot.modByMonicHom` is a linear map that
chooses the remainder representative of a quotient element. Composing it with
`Polynomial.lcoeff K (d - 1)` defines a linear functional `L`. The subtraction
is natural-number subtraction, so this definition also makes sense when `d = 0`.
Composing `LinearMap.mul` with `L` using `LinearMap.compr₂` defines the bilinear
form `B(u,v) = L(u*v)`.

Commutativity of the quotient ring proves symmetry. Associativity and
commutativity give `(a*u)*v = u*(a*v)`, which proves balance for every `a`.

For left separation, suppose `B(u,v) = 0` for every `v`, and let `r` be the
remainder representative of `u`. The proof shows `r = 0`. Otherwise
`AdjoinRoot.mk_surjective` and `Polynomial.degree_modByMonic_lt` give
`r.degree < q.degree`; since `r` is nonzero, its natural degree `e` satisfies
`e < d`. Set `n = d - 1 - e`. Then `e + n = d - 1`, and `r * X^n` has degree
`d - 1 < d`. Hence this product needs no reduction modulo `q`. The inverse
identity `AdjoinRoot.mk_leftInverse` and
`Polynomial.modByMonic_eq_self_iff` identify it with the remainder
representative of `u * AdjoinRoot.mk q (X^n)`.

The vanishing assumption now says that the coefficient of `r * X^n` in degree
`d - 1` is zero. `Polynomial.coeff_mul_X_pow` identifies this coefficient with
`r.leadingCoeff`, contradicting `r ≠ 0`. Thus `r = 0`, and
`AdjoinRoot.mk_leftInverse` gives `u = 0`. Symmetry converts this left-separation
proof into right separation, giving Mathlib's two-sided nondegeneracy predicate.

This argument includes monic constants. When `d = 0`, a nonzero remainder would
imply `e < 0`, so every remainder and every quotient vector is zero. The form is
then zero and still separates vectors on both sides.

For arbitrary nonzero `q`, `Polynomial.monic_normalize` supplies a monic
associate. `AdjoinRoot.algEquivOfAssociated` gives a `K`-algebra equivalence
`e : AdjoinRoot q ≃ₐ[K] AdjoinRoot (normalize q)`. The final form is the pullback
`B(e u, e v)`, implemented by `LinearMap.BilinForm.comp`. Symmetry transfers
directly, injectivity and surjectivity of `e` transfer each separation condition,
and multiplicativity of `e` transfers balance. This also covers every nonzero
constant polynomial.

## Provenance and scope

This is internal auxiliary mathematics for the matrix-transpose conjugacy proof,
not a quotation or proof attributed to Bernstein–Zelevinsky. Worker 308 supplied
the coefficient-of-product construction plan and the target interface; Worker 697
implemented this proof. The published statement and its documentation were
formalized separately by Worker 642. The implementation uses the project's
pinned Mathlib quotient, polynomial-remainder, linear-map and bilinear-form APIs.
It leaves the published statement and its import closure unchanged. Finite-sum
transport and the matrix-conjugator assembly are separate downstream work.
