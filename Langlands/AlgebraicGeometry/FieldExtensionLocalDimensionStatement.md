# Local dimension under extension of the ground field

`FiniteTypeFieldExtensionLocalDimensionInvariance` states that extending
the ground field of a finitely generated commutative algebra preserves
local dimension at every prime of the scalar extension.

The fields `k` and `K` and the commutative algebra `A` have three
independent universes. `K` is an arbitrary extension of `k`, and `A`
is finite type over `k`. For every actual prime `q` of `K ⊗[k] A`,
the local dimension at `q` equals that at its contraction along the
actual inclusion `A → K ⊗[k] A`, which sends `a` to `1 ⊗ a`.
There is no algebraicity, separability, injectivity, domain or
Noetherian hypothesis beyond those already implied by these inputs.
The zero algebra is included; it has no prime to quantify over.

Here local dimension means the minimum of the dimensions of open
neighbourhoods, defined by `topologicalKrullDimAt` in
`LocalTopologicalDimension`. It does not mean the dimension of the
local ring. The value lies in `WithBot ℕ∞`, with the same convention
as the imported topological and ring Krull dimensions.

The source is the registered Stacks Project snapshot
`stacks-fibre-constructibility-local-dimension-2026-11-04`,
SHA-256 `1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
Section 29.29, Lemma 29.29.3(1). That lemma gives local fibre-dimension
invariance in a cartesian square of schemes for a locally finite-type
morphism and cites Algebra Lemma 10.116.6. The present algebraic
statement is its affine specialization to a finite-type algebra over a
field and an extension of that field, using actual prime spectra and
the canonical tensor-product inclusion.

Worker 105 introduces this focused prerequisite for the general
scheme base-change comparison and the retrocompactness argument in
Stacks Lemma 29.29.6. Those are needed in the pure-dimensional-fibre
route toward Conrad's *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2).
Conrad does not state this algebra lemma separately.

This file defines a proposition and supplies no proof of it. Total
dimension invariance alone does not establish the asserted local
comparison. General scheme base change, retrocompactness, geometric
connectedness constructibility and filtered fibre descent retain
their separate proof obligations.
