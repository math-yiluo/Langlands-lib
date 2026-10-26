# Finite coefficient maps and their Banach quotients

Authors: Worker 36 and Worker 56. Worker 36 constructed this interface; its
finite-generator proof adapts Worker 56's published finite Banach-algebra
argument.

This module constructs the actual continuous coefficient map
`(Fin n → A) →L[K] B`, sending `c` to the finite sum of `f(c i) * b i`,
for a bounded algebra map `f` and a target tuple `b`. The source has the usual
finite-product norm. The construction uses the existing continuous linear map
of the bounded algebra homomorphism, continuity of multiplication, and finite
sums. It works for normed algebras over any normed field.

The underlying ring map is module-finite if and only if some such coefficient
map is surjective. The proof installs the algebra structure induced by this
exact map, chooses a finite generating family with `Module.Finite.exists_fin`,
and uses `Fintype.linearCombination`. Conversely a surjective finite
linear-combination map gives a finite module. No unrelated algebra structure
on the target is used.

For a nontrivially normed field and complete source and target algebras, every
surjective coefficient map is open and a quotient map by Mathlib's Banach open
mapping theorem. The same theorem supplies a positive constant C such that
every y has coefficients c with image y and `‖c‖ ≤ C * ‖y‖`. The kernel is
closed. `coefficientQuotientEquiv` bundles the canonical first-isomorphism
linear equivalence from the quotient by that kernel to B as a continuous
linear equivalence. Its direct map is continuous by the quotient universal
property; Banach open mapping gives continuity of its inverse. Its evaluation
on a quotient class is precisely the displayed coefficient sum. Thus the
quotient norm and the given target norm define isomorphic Banach spaces.
Completeness of the coefficient field is not needed. A zero target and an
empty generating tuple are allowed.

This is derived local infrastructure for the finite Banach-algebra condition
in Berkovich's *Non-archimedean analytic spaces*, Trieste lectures (2009),
Definition 3.3.1(i), printed/PDF p. 17. Definition 2.1.1 and the following
paragraph, p. 7, define admissibility through the quotient-by-kernel to image
isomorphism and explain the surjective-map consequence of Banach openness for
nontrivially valued fields. The present equivalence implements that consequence
for actual finite coefficient presentations. It does not treat trivially
valued fields or compare finite étaleness on all affinoid domains, and does not
construct an analytic atlas or site.

The existing `FiniteBanachAlgebra.continuous_algHom`, authored by Worker 56,
uses finite generators and a quotient coefficient map internally to prove
continuity of homomorphisms. This module exposes the coefficient maps, their
controlled lifts and their canonical quotient equivalences for reuse by the
bounded-map geometry. It leaves that existing theorem unchanged.

Registered original: `berkovich-2009-trieste-analytic-spaces`, retained SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
