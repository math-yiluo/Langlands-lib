# Actual unitary matrix adjoints on whole place enveloping algebras

For an independently sized RCLike field `𝕜` and any natural rank `n`,
`unitaryMatrixEnvelopingConjugation` is the actual complex algebra
automorphism induced by unitary matrix conjugation on the entire
complexified underlying real matrix Lie algebra. It reuses the published
`LieEnvelopingEquiv.enveloping` construction, including its proved inverse
laws. Its value on each canonical Lie generator is the generator of the
actual complexified matrix conjugate.

The identity and multiplication laws of the complexified matrix adjoint
are proved by tensor induction and the original matrix formula
`k X k⁻¹`. Universal enveloping extensionality promotes these laws to the
whole local algebra. The resulting algebra automorphisms preserve the
identity, follow `Ad(k l) = Ad(k) ∘ Ad(l)`, and send a group inverse to the
inverse algebra equivalence. All ranks, including zero, are retained.
At a complex place the domain is `U_ℂ(ℂ ⊗_ℝ Mat_n(ℂ))`; the underlying real
matrix algebra is retained in full before complexification.

For any field `F : Type u`, full actual compact coordinate product `p`
and actual real or complex infinite place, global enveloping conjugation
preserves the whole included local enveloping algebra. The resulting
local conjugation uses precisely `p.1 v` or `p.2 v`. Equalities of actual
algebra homomorphism compositions are proved by extensionality on the
original Lie generators, using the proved global/local matrix Lie
adjoint compatibility. Evaluation gives the same identities for every
local algebra element. No number-field or positive-rank premise is needed.

This is an internal construction from `ArchimedeanPlaceAdjoint`,
`ArchimedeanPlaceEnveloping`, the original global adjoint and the published
generic Lie/enveloping equivalence helper. It adds no original-literature
assertion, topology or normalization. It does not construct automorphic
irreducible factors or a Langlands attachment.
