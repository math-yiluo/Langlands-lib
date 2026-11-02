# Almost-everywhere local powers and global half-powers

Authors: Worker 53 and Worker 1232.

`Langlands.Global.AlmostEverywherePowerHalfStatement.{u}` states that for every
number field `K : Type u`, finite set `S` of its actual finite places, positive
natural number `n`, and nonzero element `a : Kˣ`, local solvability of
`b^(2*n) = a` in the units of every actual finite completion outside `S`
implies global solvability of `b^n = a` in `Kˣ`. The local value of `a` is its
image under the completion's algebra map, lifted to units. The field universe
is unrestricted.

The source is Artin and Tate, *Class Field Theory*, AMS Chelsea edition (2009),
Chapter IX, Section 1, Theorem 1 and its proof, printed pp.65–66 (one-based
PDF pp.74–75). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata at one-based PDF p.202 contain no correction to this theorem.
Both authors read the source theorem and proof; Worker 1232 identified this
minimal interface in the arithmetic prerequisite audit.

This statement is a derived specialization. Set the source exponent to `2*n`
and exclude all infinite places as well as `S`; a number field has finitely many
infinite places. In the source's cyclic cyclotomic case, a global `(2*n)`th root
gives an `n`th root by squaring. In its remaining case, the conclusion is already
a global `n`th root. Thus no condition at infinity, roots-of-unity hypothesis,
or Wang compatibility hypothesis is required here. The use of units records
the source's nonzero multiplicative groups.

The source proof reduces to prime powers, proves the roots-of-unity case by
cyclic splitting, and descends from cyclotomic extensions. For odd primes it
uses a norm of degree coprime to the exponent. In the exceptional 2-primary
case, descent through `K(i)` loses at most one factor of two; the possible
negative sign is excluded by the quadratic splitting argument.

The Lean file defines a proposition only. It neither proves this arithmetic
implication nor assumes it as an axiom or typeclass instance. This implication
is intended as the arithmetic input to the power-intersection step in
finite-order Hecke-character prescription.
