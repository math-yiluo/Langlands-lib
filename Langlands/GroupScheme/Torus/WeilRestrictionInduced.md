# Finite-separable Weil restrictions are induced tori

Worker 363. This internal construction derives inducedness from the published
canonical embedding splitting and its actual character Galois action.

For fields `k`, `K`, and `Ω` in an arbitrary common universe, suppose that
`K/k` is finite separable and every minimal polynomial of an element of `K`
splits in `Ω`. The definition `separableEmbeddingCharacterBasis` transports
the standard integer basis of functions on `K →ₐ[k] Ω` through the inverse
of `separableEmbeddingCharacterEquiv`. It is a basis of the character lattice
of the actual base-changed Weil restriction, rather than an abstract model
supplied as an additional premise.

`separableEmbeddingCharacterBasis_galoisRepresentation` proves that each
`k`-automorphism `σ` of `Ω` carries the basis element indexed by `τ` to the
one indexed by `σ ∘ τ`. The proof applies the published embedding-coordinate
equivalence. Its Galois comparison identifies the action with inverse
pullback, which permutes the standard delta functions by postcomposition.

When `Ω/k` is finite Galois, `isInducedTorus_of_separable_splitting` uses
the canonical `separableEmbeddingIso` and this permuted basis to witness
every clause of `IsInducedTorus`.

Finally, `isInducedTorus_of_finite_separable` requires only finite
separability of `K/k`. It embeds `K` into `SeparableClosure k` using
`IsSepClosed.lift` and takes its normal closure there. Mathlib supplies the
finite-dimensional and Galois instances and `IsNormalClosure.splits` for
this normal closure. The preceding theorem then proves that
`WeilGm.commGroupScheme (CommRingCat.of k) K` is induced. There is no
normality hypothesis on `K/k` and no perfectness hypothesis on `k`.

The construction and proofs use `WeilRestrictionSeparable`, `Induced`,
Mathlib's standard function basis and its normal-closure theory. This is
derived content about these published interfaces; no new literature
assertion or unproved proposition is assumed. It supplies an induced-torus
input for the rank-one coroot argument, without claiming to prove that
argument on its own.
