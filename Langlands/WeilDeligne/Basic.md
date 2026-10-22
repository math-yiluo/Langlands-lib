# Algebraic Weil–Deligne pairs, morphisms and classes

Worker 17 implements finite-dimensional pairs `(r,N)` over a field, a group,
and an explicitly supplied unit-valued norm character `ν`. The vector space
is the actual carrier of a `FiniteRepresentation`. The monodromy operator is
nilpotent, and the structure includes the defining covariance equation

`r(g) * N * r(g⁻¹) = (ν(g) : K) • N`.

Multiplication of endomorphisms is composition. Since `r` is a group
representation, `r(g⁻¹)` is the inverse of `r(g)`. This is the conjugation
convention of Tate's Weil–Deligne definition. For the local specialization,
the intended character sends geometric Frobenius of degree `+1` to `q⁻¹`.
This generic module does not choose `q` or construct that specialization.

`Hom` consists of a linear representation intertwiner commuting with the
monodromy operators. Its identity and composition include proofs of the
monodromy equation. These give a category whose associativity and identity
laws are proved using equality of the underlying linear maps. The `forget`
functor preserves the original representation and carrier.

`Equiv` requires an actual representation equivalence commuting with
monodromy. Inverting the underlying linear map preserves the monodromy
equation by injectivity and the original equation. Composition uses the
already proved morphism composition law. `Equiv.toIso` and `Equiv.ofIso`
connect these linear equivalences to categorical isomorphisms.

The existence of such an equivalence is proved reflexive, symmetric and
transitive before forming `IsomorphismClasses`. Equality in this quotient
means exactly existence of an isomorphism of pairs. Dimension invariance
under the underlying linear equivalence makes `classRank` well-defined.
`IsomorphismClassesOfRank n` includes all pairs of rank `n`; it does not
restrict to zero monodromy. Rank zero remains available internally.

`zeroMonodromy` is the actual pair with `N = 0`, with nilpotence and
covariance proved. `zeroMonodromyFunctor` maps every intertwiner to the
same linear map and proves the functor laws. `zeroMonodromyFullyFaithful`
proves that every intertwiner between these objects lifts uniquely.

`IsFrobeniusSemisimple` requires semisimplicity of the action of every
element of nonzero degree, in particular every geometric Frobenius of
degree `+1`. It uses Mathlib's semisimplicity predicate for an
endomorphism. It neither sets `N` to zero nor chooses a Frobenius
semisimplification. For arbitrary supplied degree data this universal
predicate may be vacuous; nonempty Frobenius fibers belong to the actual
Weil specialization, not to the definition of an algebraic pair.

## Source correspondence and remaining layer

Tate, *Number theoretic background* (1979), section 4.1.2–4.1.5,
printed page 20 (PDF page 29 of `Part II.pdf`), defines the nilpotent
operator and norm-covariance equation, Frobenius semisimplicity, and the
zero-monodromy inclusion of Weil representations. The explicit category,
isomorphism relation and quotient are implementation infrastructure for
those objects. Tate's open-inertia-kernel condition is intentionally a
separate predicate on this algebraic ambient category. This module alone
therefore does not assert that every algebraic pair is a local
Weil–Deligne parameter.

- Literature ID: `tate-1979-number-theoretic-background`.
- Source SHA-256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
- Direct project dependency: `Langlands.Weil.Representation.Basic`, included
  in accepted definition `9bc9ac90-547a-485c-a632-039a3e1214a7` version 1.
  It is published and current at commit
  `843c574c920aa9926ab56adf662c74b3cd4ed0e1`, integration
  `6dea9fb977784cfa93d8d9b241e063f3`. The complete final independent review
  has no unresolved qualifications, and all four dependency source files
  match their reviewed hashes. This contribution does not alter them.

All structure, category, equivalence and quotient obligations are intrinsic
proofs. Existence or uniqueness of Frobenius semisimplification,
classification into special blocks, and comparison of topology predicates
are not assumed. This pair compiles in the pinned environment and remains development pending
independent review; the complex topological parameter subtypes are a separate layer.
