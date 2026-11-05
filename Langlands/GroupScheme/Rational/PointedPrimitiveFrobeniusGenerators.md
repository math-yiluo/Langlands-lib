# Finite Frobenius generators of actual primitive group coordinates

This internal assembly connects `PointedLaurentCoordinates` with
`LaurentFrobeniusPullback`. Let `k` be an arbitrary field and let `B`
corepresent an actual group scheme over `k`. The coordinate pullback
`σ : B →ₐ[k] AddMonoidAlgebra k (I → ℤ)` is assumed to intertwine the
Laurent identity augmentation and the actual group counit.
`primitiveLaurentPullback` restricts this map to `primitiveFunctions e`
and has values in the Laurent augmentation kernel. It is injective when
`σ` is injective.

Suppose that `k` has prime characteristic `p` and that `σ` is injective.
Any finite family `T` of primitive coordinate functions admits a finite
replacement `G` of primitive functions generating the same `k`-subalgebra
of `B`. Their Laurent pullbacks have equal Frobenius spans, the pullbacks
of `G` lie in the span of those of `T`, and this span lies in a finite
primitive-character orbit space. The finite encodings of the pullbacks
of `G` satisfy `TorusLinearization.FrobIndep`.

The proof applies the existing finite Laurent pullback theorem to the
actual primitive-coordinate submodule. Vanishing of the counit and
stability under `b ↦ b^p` were proved in `PointedLaurentCoordinates`;
the augmentation identity and compatibility of algebra maps with
powers give precisely the hypotheses of that theorem.

For a reduced corepresented group with an actual pointed dominant
scheme morphism from a finite-rank split torus,
`exists_pointed_primitiveFrobGenerators` constructs such an injective
Laurent pullback and the finite replacement together. No group
homomorphism assumption on the dominating map is needed. The field may
be finite or imperfect.

This result neither supplies an initial primitive algebra-generating
family nor proves algebraic independence of the replacement. It does
not assert the full splitness criterion.
