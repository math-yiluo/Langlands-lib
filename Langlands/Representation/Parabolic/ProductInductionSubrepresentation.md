# Actual proper nonzero slot subspaces in normalized block products

This internal adapter lifts an invariant subspace of one original block factor
to an actual invariant subspace of the full normalized upper parabolic product.
It preserves the supplied block shape and the original actions throughout.

`Langlands.Parabolic.normalizedProductSlotSubrepresentation T B ρ j S` first
forms `FiniteTensor.externalSlotSubrepresentation ρ j S`, the actual tensor
subspace determined by the supplied original slot subspace. It then takes the
actual normalized induced functions with values in that tensor subspace, using
`normalizedInducedSubrepresentation`. Its ambient action is exactly
`T.normalizedProductInduced B ρ`. This construction preserves bottom and top
without any smoothness or nonzero assumption.

`normalizedProductSlotSubrepresentation_le_iff` proves inclusion reflection and
preservation when all original factors are smooth and all complementary factor
carriers are nonzero. The finite external tensor is smooth by the published
finite tensor theorem. The induced value-subspace inclusion theorem then
reduces the claim to the tensor slot inclusion theorem, whose nonzero
complementary-carrier hypotheses are supplied explicitly. The complement may
be empty, as for a single block. A specified slot is always required.

`normalizedProductSlotSubrepresentation_ne_bot` and
`normalizedProductSlotSubrepresentation_ne_top` preserve nonzero and proper
subspaces under those same hypotheses. The final theorem
`normalizedProductSlotSubrepresentation_proper_nonzero` combines these for the
actual subrepresentation constructed from a supplied proper nonzero slot
subrepresentation. In particular, it proves nonvanishing and properness in the
full normalized product, beyond merely producing an injective tensor or induced
map. The nonzero complementary-carrier hypothesis is essential.

Field and factor carrier universes remain independent; the actual induced
carrier lies in their maximum universe. The prime and compatible topology are
arbitrary. No segment, linkedness, irreducibility, or classification input is
used. There is no regrouping of block shapes or ambient ranks.

Provenance is internal composition of the actual tensor slot subspace,
the normalized induction value-subspace construction, and smoothness of the
finite external tensor. The first reflection theorem detects the original
slot by a dual functional on a nonzero complementary tensor. The second uses
compact local sections of the restricted inducing representation. This module
adds only their same-shape normalized product specialization.
