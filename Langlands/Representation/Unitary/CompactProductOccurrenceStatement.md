# Irreducible occurrence in a factor of a compact-convolution product action

`Langlands.Analysis.CompactProductOccurrenceStatement` concerns two commuting
unitary actions `σ` and `τ` of locally compact Hausdorff second-countable
groups `G` and `D` on a nonzero complex Hilbert space `E`. Both groups carry
their Borel σ-algebras and supplied left Haar measures `μ` and `ν`. The
actions preserve inner products and have continuous orbit maps. The
universes of `G`, `D` and `E` are independent.

For every pair of compactly supported continuous complex weights `f` on
`G` and `b` on `D`, the premise asks that `σ(f).comp (τ(b))` be compact.
The operators `σ(f)` and `τ(b)` are built by
`Langlands.Analysis.integratedIsometricAction` using the integrals against
`μ` and `ν`. The integrability proofs in the premise are available by
continuity and compact support. The conclusion gives a nonzero closed
complex submodule `W` of `E` invariant under `σ`. Every closed
`σ`-invariant submodule of `W` is zero or all of `W`.

## Provenance

The criterion is derived from the compact-convolution argument in
Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
§9.3, printed pp. 246–247 (one-based PDF pp. 258–259), especially
Lemma 9.3.1 and Corollary 9.3.2 on p. 247. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

The Hermitian approximate identities for the two actions, expressed against
the supplied left Haar measures using the Haar inversion density, give
self-adjoint integrated operators `A` and `B` with `A.comp B ≠ 0`.
Indeed, one can choose `A` to act nontrivially on a given nonzero vector
and then choose `B` so that `A.comp B` still acts nontrivially on it.
The commuting actions make `A.comp B` self-adjoint and, by the premise,
compact. Its eigenspace for a nonzero eigenvalue is nonzero,
finite-dimensional and stable under `B`. The restriction of `B` to this
space is self-adjoint and injective, since a vector killed by `B` is
killed by `A.comp B`. It therefore gives a nonzero eigenvalue `β` of `B`.
The full `β`-eigenspace in `E` is closed and `σ`-invariant because `B`
commutes with `σ`. Each first-action convolution restricted to that
eigenspace is `β⁻¹` times the restriction of its compact product with `B`.
Applying `Langlands.Analysis.invariantSubspaceDiscreteDecomposition` to
that eigenspace yields an irreducible summand.
