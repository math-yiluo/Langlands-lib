# Actual archimedean place actions on automorphic operator quotients

This internal construction works with every number field `F : Type uF`,
every natural rank `n`, complex coefficients and an actual
`OperatorSubquotient F n`. The carrier is the original module quotient
`Q.upper.Space ⧸ Q.lower.toSubmodule`. The denominator is already invariant
under the whole concrete automorphic operator algebra. No additional
invariance, covariance or finiteness hypothesis is supplied here.

`realPlaceCompactRepresentation` restricts the quotient's actual infinite
compact representation along `realPlaceCompactInclusion`, with domain
`Matrix.unitaryGroup (Fin n) ℝ`, the orthogonal group. The complex-place
construction uses the actual unitary group over `ℂ` and
`complexPlaceCompactInclusion`. Both use the existing quotient carrier.

`realPlaceEnvelopingAction` and `complexPlaceEnvelopingAction` compose the
genuine quotient enveloping algebra action with the existing actual place
enveloping inclusions. These are unital complex algebra homomorphisms into
`Module.End ℂ Q.Space`. Their domains are respectively
`U_ℂ(ℂ ⊗_ℝ M_n(ℝ))` and `U_ℂ(ℂ ⊗_ℝ M_n(ℂ))`; at a complex place the
full underlying real matrix Lie algebra is used before complexification.
The tensor products and enveloping algebras are algebraic.

The four `...Projection` maps are the original canonical quotient
projection, equipped with equivariance for each actual local compact or
enveloping action. Their linear map is exactly `Q.projection.toLinearMap`.
The four `..._projection` formulas identify each local action on a projected
representative with the projection of its numerator action. Consequently
the same projection is surjective and has exactly the previously specified
denominator as kernel; those facts are inherited from `OperatorSubquotient`.

`map_realPlaceCompactOrbitSpan` and `map_complexPlaceCompactOrbitSpan`
identify each compact quotient orbit span with the linear image under the
canonical projection of that same local numerator orbit span. The proofs
apply the published orbit-image theorem to the corresponding projection
intertwiner. Every quotient vector has a representative. Its local
numerator orbit span is finite dimensional by the existing genuine
realization theorem; finiteness descends through that intertwiner. This
proves `realPlaceCompactRepresentation_isFiniteVector` and its complex
counterpart for all quotient vectors.

The four finite-translation commutation theorems restrict the existing
quotient finite/compact and finite/enveloping identities along the actual
place inclusions. They hold for every finite adelic translation and every
element of the corresponding local compact group or enveloping algebra.

The two same-place covariance theorems hold on every local enveloping
element: compact translation of a local differential equals the
differential of `unitaryMatrixEnvelopingConjugation` by that same orthogonal
or unitary matrix, followed by compact translation. The proof lifts a
quotient vector to a numerator representative and applies the canonical
projection to the published numerator covariance identity. Thus these are
proved consequences of the genuine operators.

The four `Equivalence` restrictions retain exactly the linear equivalence
of any supplied whole-operator quotient equivalence. Equivariance follows
by evaluating that equivalence on the same compact or differential
generators. In particular, no equality of numerator/denominator
presentations is required to obtain equivalences of the local actions.

Provenance is internal. The construction reuses `OperatorSubquotient`,
`OperatorSubquotientArchimedean`, `PlaceCompactAction`,
`PlaceEnvelopingAction`, `PlaceEnvelopingCovariance` and the orbit-span
image and finiteness transfer in `FiniteVectors`. It introduces no new
identification with an external source or normalization convention.

These restrictions retain the entire quotient carrier. They do not select
irreducible archimedean tensor factors or prove admissibility, tensor
factorization, local Langlands attachments, automorphic existence or
spectral existence. No topology, analytic differentiability or evaluation
of a quotient class as a function is constructed.
