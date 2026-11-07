# Actual compact covariance of place actions on automorphic operator quotients

This internal construction works with every number field `F : Type uF`,
every natural rank `n`, complex coefficients and an actual
`OperatorSubquotient F n`. It uses the unchanged quotient carrier
`Q.Space` and the genuine actions constructed in
`OperatorSubquotientArchimedean` and `OperatorSubquotientPlaceAction`. No
additional invariance, covariance or finiteness hypothesis is supplied.

`compactEndConjugation k` is conjugation of all complex endomorphisms of
`Q.Space` by the actual compact translation `Q.compactLinearEquiv k`, as a
complex algebra automorphism of `Module.End ℂ Q.Space`. Explicitly,
`compactEndConjugation_apply` states that `A` is sent to
`f ↦ Q.compactRepresentation k (A (Q.compactRepresentation k⁻¹ f))`.
`compactEndConjugation_finite` proves that it fixes every finite adelic
translation operator. `compactEndConjugation_enveloping` proves that it
sends the quotient action of every global enveloping element `a` to the
quotient action of `envelopingConjugation F n k.val a`, the existing
global adjoint action. Both proofs evaluate the published quotient
finite/compact and compact/enveloping commutation identities at
`Q.compactRepresentation k⁻¹ f`.

`realPlaceCompactEndConjugation` and `complexPlaceCompactEndConjugation`
restrict this conjugation along `realPlaceCompactInclusion` and
`complexPlaceCompactInclusion`; the corresponding `_finite` theorems
specialize the finite-translation invariance. The two
`...PlaceCompactFiniteEquivalence` definitions restrict the existing
`compactFiniteEquivalence` along the same inclusions. They are
automorphisms of the finite quotient representation whose underlying map
is exactly the local compact quotient translation, as stated by the
`_apply` lemmas.

`realPlaceCompactConjugatedEnvelopingAction v k` composes the actual
real-place quotient enveloping action with `realPlaceCompactEndConjugation
v k`; the complex definition is analogous. The `_eq` theorems prove that
each equals the same local quotient action precomposed with
`unitaryMatrixEnvelopingConjugation` by the same orthogonal or unitary
matrix `k`. These are equalities of complex algebra homomorphisms on the
whole local algebras `U_ℂ(ℂ ⊗_ℝ M_n(ℝ))` and `U_ℂ(ℂ ⊗_ℝ M_n(ℂ))`; at a
complex place the full underlying real matrix Lie algebra is used.

`compactRepresentation_realPlaceEnvelopingAction` and its complex
counterpart hold for every element `p` of `ArchimedeanCompactFactors F n`,
the product of orthogonal groups at real places and unitary groups at
complex places, every place `v` of the stated type, every local enveloping
element `a` and every quotient vector `f`. Write `k` for compact
translation by `toStandardCompact F n p` and `a'` for
`unitaryMatrixEnvelopingConjugation` of `a` by the place-`v` coordinate of
`p`. Then `k` applied to the place-`v` action of `a` on `f` equals the
place-`v` action of `a'` on `k f`. The
`compactEndConjugation_...PlaceEnvelopingAction` theorems state the same
identities as equalities of quotient endomorphisms. The proofs apply the
published quotient compact/enveloping identity to the actual place
inclusion and rewrite with the published global/local adjoint
compatibility `envelopingConjugation_realInclusion` or
`envelopingConjugation_complexInclusion`.

Specializing the coordinates gives the commutation theorems. Every
real-place compact operator commutes with every complex-place enveloping
operator, and every complex-place compact operator commutes with every
real-place enveloping operator. The two `_of_ne` theorems prove the same
commutation for distinct places of the same type. They use that the
compact element inserted at one place has identity coordinates elsewhere
and that `unitaryMatrixEnvelopingConjugation` at the identity matrix is the
identity automorphism. All statements hold on every local enveloping
element, not only on generators.

Provenance is internal. The construction reuses `OperatorSubquotient`,
`OperatorSubquotientArchimedean`, `OperatorSubquotientPlaceAction`,
`ArchimedeanPlaceCompact` and `ArchimedeanPlaceEnvelopingAdjoint`, together
with Mathlib's `LinearEquiv.conjAlgEquiv`. No quotient induction or new
identification with an external source or normalization convention is
introduced.

These results retain the entire quotient carrier. They do not construct
`(𝔤, K)`-module structures, select irreducible archimedean tensor factors,
or prove admissibility, tensor factorization, local Langlands attachments,
automorphic existence or spectral existence. No topology, analytic
differentiability or evaluation of a quotient class as a function is
constructed.
