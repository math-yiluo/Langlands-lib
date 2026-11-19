# Integral conjugacy of étale embeddings with the same reduction

Let `C` be an étale algebra over a commutative ring `O`. The kernel of
multiplication on `C ⊗[O] C` is a finitely generated idempotent ideal.
If `d` is an idempotent generator of that kernel, its complement
`e = 1 - d` maps to one and satisfies `(c ⊗ 1)e = (1 ⊗ c)e`.
The construction uses Mathlib's Kähler differential ideal and the
finitely generated idempotent ideal theorem.

For algebra maps `f, g : C →ₐ[O] A` to a possibly noncommutative algebra,
`intertwiner f g` applies the linear map `x ⊗ y ↦ f(x)g(y)` to `e`.
The two tensor identities give `f(c) intertwiner = intertwiner g(c)`
and show that the intertwiner maps to one under any ring homomorphism
identifying the two maps.

Apply this to the integer subring of a valuation on a division ring.
If the maps have the same reduction, the residue of the intertwiner
is one, so it is a unit of that integer subring. Its inverse gives the
unit in `exists_integerUnit_conj`, with `f(c) = u⁻¹ g(c) u` for every `c`.

This is an internal algebraic step toward comparing the conjugated
geometric tangent actions in Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), §2 A, printed p. 109.
