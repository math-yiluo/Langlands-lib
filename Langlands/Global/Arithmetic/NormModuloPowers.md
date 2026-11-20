# Descent of norms modulo powers

For a finite field extension `E/F` and a unit `a` of `F`, `IsNormMulPower`
means that `a = N(b) q^n` for units `b` of `E` and `q` of `F`. The norm
of the image of `q` is `q^[E:F]`. Bézout's identity therefore gives such a
factorization for every `a` if `[E:F]` and `n` are coprime. This includes
cubic extensions with `n = 2`. If the degree divides `n`, a factor `q^n`
in this expression can be absorbed into the determinant norm.

`NumberFieldQuadraticNormPowerDescentStatement` uses a degree-two
extension of number fields and the actual field completions at all
finite and infinite pairs of places. A base unit that is a norm modulo
`n`-th powers at each such pair is a norm modulo `n`-th powers over the
original fields. Odd `n` uses the coprime calculation. If `2` divides
`n`, every finite local degree divides `n` by the decomposition-group
embedding, and every infinite local degree is one or two. Absorb the
local powers into the local norms. The cyclic Hasse norm theorem then
gives a global norm witness.

These are the base-unit calculations used for norm-kernel centers in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§6.5, Lemma 6.19, printed pp. 336–337. The Lean statement records the
multiplicative witnesses in place of the quotient by norms and powers.
