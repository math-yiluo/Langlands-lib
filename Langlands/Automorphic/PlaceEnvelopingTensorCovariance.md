# Compact covariance of actual two-place enveloping tensor actions

For a number field `F : Type u`, every natural rank `n` and an existing
actual `OperatorRealization F n`, this module constructs compact-conjugated
two-place enveloping tensor actions on the unchanged original `S.Space`.
The coefficient field and each algebra tensor product are complex.

`realPlacesCompactConjugatedEnvelopingTensorAction`, its complex/complex
counterpart and its real/complex counterpart compose the existing original
tensor action with conjugation of the original endomorphism algebra by
the actual compact translation associated to a supplied
`ArchimedeanCompactFactors F n` coordinate product. They are unital complex
algebra homomorphisms into the original endomorphism algebra. Same-type
place pairs retain their explicit inequality; the mixed pair uses one real
and one complex place. Each complex-place algebra is still the universal
enveloping algebra of the complexification of the full underlying real
complex matrix Lie algebra.

For every element of each tensor algebra and every original vector,
the original tensor operator followed by compact translation equals the
operator of the tensor adjoint applied after compact translation. The
adjoint uses the two selected compact coordinate matrices. The corresponding endomorphism equality conjugates
by `rho(k) A rho(k⁻¹)` and uses the matrix convention `X ↦ k X k⁻¹`.
The real/real case selects `p.1 v` and `p.1 w`, the complex/complex case
selects `p.2 v` and `p.2 w`, and the mixed case selects `p.1 v` and
`p.2 w`. These assertions quantify over every tensor element, without
restricting to pure tensors.

The three `_eq` theorems identify the constructed conjugated actions, as
unital complex algebra homomorphisms, with the original tensor actions
composed with `unitaryMatrixEnvelopingTensorConjugation`. The carrier,
compact translation and global differential remain the existing genuine
operators of the same realization throughout.

The proofs specialize the original global compact/enveloping covariance
and endomorphism-conjugation identity to each actual global place tensor
map. The proved whole-tensor global adjoint compatibility identifies the
resulting global algebra element. Algebra-homomorphism extensionality
then proves equality of the constructed actions. Explicit module-specific
local instance names retain the original submodule additive structures
and permit joint imports with the single-place covariance module.

This is an internal construction from `PlaceEnvelopingTensorAction`,
`OperatorCompactCompatibility` and `ArchimedeanPlaceEnvelopingTensorAdjoint`.
It makes no new original-literature assertion and introduces no topology
or normalization. It constructs actions on the actual existing carrier;
faithfulness, a tensor decomposition of that carrier, irreducible or
admissible archimedean factors, their existence and Langlands attachments
remain separate obligations.
