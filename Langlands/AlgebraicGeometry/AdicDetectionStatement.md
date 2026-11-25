# Adic detection of a subscheme of a finite scheme

`Langlands.AlgebraicGeometry.AdicDetection.AdicImmersionIsIsoStatement.{u}`
states SGA 3, Exposé IX, Lemme 5.0 for every universe `u`.

Let `A` be a commutative local Noetherian ring, with maximal ideal `m`.
Let `p : X ⟶ Spec A` be finite, and let `i : Z ⟶ X` be an immersion.
For every natural number `n`, suppose the base change of `i` along
`Spec(A / m^(n+1)) ⟶ Spec A` is an isomorphism. Then `i` is an isomorphism.

`adicBase A n` is exactly the spectrum morphism of the canonical quotient
ring homomorphism. `baseChange p i r` is the underlying scheme morphism
obtained by applying Mathlib's `Over.pullback r` to the morphism with
underlying map `i` from `(Z, i ≫ p)` to `(X, p)`. Thus the tests are actual
scheme pullbacks. The hypotheses use Mathlib's `IsFinite` and
`IsImmersion`; there are no additional hypotheses on `Z`, no reduction
assumption, and no separatedness or finite-presentation assumption on `i`.

This module states the lemma; it does not supply its proof, which is in
`AdicDetectionProof`.
The two auxiliary definitions only expose the canonical maps used in the
statement and impose no mathematical conditions.

Source: A. Grothendieck, *SGA 3*, Exposé IX, Lemme 5.0, Gille–Polo
recomposed edition, provisional version of 8 November 2009, recomposed
p.48 (PDF p.18, original margin p.58), registered as
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The lemma and its proof were read in both extracted text and the rendered
page. No source-specific errata file was found in the Library's errata notes.
