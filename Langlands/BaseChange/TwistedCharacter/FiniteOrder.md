# Finite-order normalization of a twisting isomorphism

Let `A` be a twisting isomorphism from an admissible irreducible complex
representation to its pullback by an automorphism `θ`. Powers of `A`
intertwine the corresponding powers of `θ`. If `θ^d` is the identity
and `d > 0`, the operator `A^d` is an endomorphism of the original
representation. Schur's lemma makes it a scalar, and injectivity makes
that scalar nonzero. Henniart–Lemaire (2011), II.5.2, allow
`A^d = λ I` for any nonzero complex `λ`. Scaling by a `d`-th root
of `λ⁻¹` gives the identity-power normalization of Rogawski (1988),
p. 215. `scaleTwistingEquiv` realizes the scaled map as a twisting
isomorphism.

The induced operator acts by the inducing isomorphism and precomposition
with `θ⁻¹`. Iterating the two operations gives the corresponding powers
on sections. Thus the induced isomorphism has `d`-th power one whenever
the inducing isomorphism and ambient automorphism do. The argument uses
the Library's unnormalized smooth induction and the section formula of
Henniart–Lemaire II.4.4.

Two twisting isomorphisms on the same representation differ by a scalar
by applying Schur's lemma to their ratio. If both have `d`-th power one,
that scalar has `d`-th power one. An equivalence of underlying
representations transports a twisting isomorphism by conjugation, preserving
its powers. The Library's transport and scalar homogeneity of twisted
distributions give the same root-of-unity comparison for their twisted traces.
