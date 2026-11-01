# Genuine finite tensor presentations of actual CM images

This is an internal construction from the existing actual arithmetic tensor
transport, genuine tensor presentations, and actual CM images of finite
automorphic realizations. It makes no new identification with original literature.

Let `F` be an actual CM number field in universe `uF`, and let `n` be any natural
matrix rank. The local complex module carriers `V v` are independently quantified
in universe `uV`; no topology or finite-dimensionality is imposed on them.
The input `P` is a genuine `FiniteTensorPresentation` of a specified embedded
finite realization `S`. It supplies an equivariant linear equivalence onto that
form space, integral-fixed reference vectors outside `E`, and nonzero reference
vectors there. No nonzero condition on `S` is needed for this construction.

Write `c` for the actual CM field automorphism and `q` for
`finitePlaceEquiv c`. The place map is the existing ideal-comap equivalence.
`complexConjFactors` uses the old model `V (q v)` at the new place `v`, with action
`ρ (q v)` precomposed by `(AdelicGLTransport.localEquiv n c v).symm`.
This inverse completion-group map goes from the group at `v` to the group at
`q v`. The coefficients remain complex numbers with their original scalar action.

`complexConjExceptional` is exactly `E.map q.symm.toEmbedding`.
The reference vector at `v` is `e (q v)`. The existing arithmetic transport
preserves integrality, so `complexConjReference_fixed` proves the required
integral fixedness outside precisely that finite set. The original nonvanishing
condition pulls back through the same finite-set membership equivalence.

`complexConjTensorEquiv` identifies this transported tensor representation with
the original tensor representation precomposed by `CMConjugation.finiteConj F n`.
Its underlying linear equivalence is the actual arithmetic tensor reindexing
equivalence. The arithmetic equivalence initially intertwines after precomposing
the transported representation by the arithmetic finite group map. A private
involutivity proof, obtained from Mathlib's CM field involution and the proved
composition law for arithmetic finite adelic transport, rebases that covariance
to the new finite group.

`complexConjEquiv` composes this equivalence with the pullback of `P.equiv` and
`S.complexConjRepresentationEquiv`. Its target is the representation on the actual
image of `S` under CM pullback of automorphic functions. Its value on a tensor is
the image under `S.complexConjEquiv` of the original presented vector after tensor
reindexing. `evaluate_complexConjEquiv` consequently evaluates the original
function at `CMConjugation.adelicConj F n a`. Complex function values are unchanged.

`P.complexConj` bundles the constructed equivalence and the proved nonzero
reference condition as a genuine presentation of `S.complexConj`. The result
transports an existing presentation; it does not assert factorization or occurrence
for arbitrary automorphic realizations. It supplies no equality between selected
local slices and the whole locally restricted tensor carrier, no topological
equivalence on the abstract tensor model, and no spectral or classification result.
