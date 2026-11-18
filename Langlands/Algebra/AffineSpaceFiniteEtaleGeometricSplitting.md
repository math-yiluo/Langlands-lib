# Geometric splitting of finite étale covers of affine space

Worker 598 drafted the statement.

The proposition definition
`Langlands.Algebra.AffineSpaceFiniteEtaleGeometricSplittingStatement.{u}`
expresses the geometric input for
`Langlands.Algebra.AffineSpaceFiniteEtalePolynomialProductStatement`.
For an algebraically closed field `k : Type u` of characteristic zero and
`n : ℕ`, set `R := MvPolynomial (Fin n) k`. For every commutative `R`-algebra
`A : Type u` satisfying `Algebra.Etale R A` and `Module.Finite R A`, it asserts

```lean
∃ m : ℕ, Nonempty (A ≃ₐ[R] (Fin m → R))
```

The product has its pointwise algebra structure, with the structure map
sending a scalar to the corresponding constant function. The equivalence
therefore preserves the original polynomial coordinates. The field, algebra,
and product lie in the same arbitrary universe `u`. In dimension `n = 0`
the base is canonically `k`. The empty product `m = 0` is the zero algebra.

## Provenance

This coordinate-ring formulation is derived from SGA 1, *Revêtements étales
et groupe fondamental*, recomposed annotated edition, registered as
`sga1-arxiv-math-0206203v2` with SHA-256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
[SGA 1, arXiv math/0206203v2](https://arxiv.org/pdf/math/0206203v2)

Exposé XIII, Corollary 2.12 and its proof (printed pp. 290–291, PDF
pp. 306–307) present the tame fundamental group of a smooth proper curve
with finitely many points removed. For the projective line with the point
at infinity removed, the genus is zero and the relation forces the sole
inertia generator to be the identity. In characteristic zero every finite
étale cover of this open curve is tame, so the full étale fundamental
group of the affine line is trivial.

Exposé XIII, Proposition 4.6(a) (printed pp. 310–311, PDF pp. 326–327)
applies to products of affine spaces. The affine line is of finite type,
and the strong desingularization hypothesis holds in characteristic zero
by Remark 3.1.3 (printed p. 302, PDF p. 318). All primes are allowed in
characteristic zero, so iteration of the Künneth formula gives triviality
of the full étale fundamental group in every positive dimension. In
dimension zero the base is the spectrum of an algebraically closed field,
which also has trivial étale fundamental group.

The finite-set description of covers in Exposé V, §7 (printed p. 115,
PDF p. 131) then identifies a cover with an `m`-element fiber with the
disjoint union of `m` copies of `Spec R` over `Spec R`. Taking coordinate
rings gives the displayed `R`-algebra equivalence.
