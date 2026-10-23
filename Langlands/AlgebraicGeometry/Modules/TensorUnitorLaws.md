# Naturality of the explicit sheaf tensor unitors

The three unconditional lemmas in `Langlands.Scheme.Modules` concern the
existing sheafified tensor construction on `X.Modules` for an arbitrary
scheme `X : Scheme.{u}`.

`tensorLeftUnitor_naturality` and `tensorRightUnitor_naturality` prove
naturality of the explicit sheaf unitors: first use functoriality of
sheafification and the presheaf unitor naturality equation, then use
naturality of the sheafification counit. `tensorUnitors_equal` proves that
their homomorphisms agree on the structure sheaf by sheafifying the
presheaf equality `MonoidalCategory.unitors_equal` and postcomposing
with the same counit.

These declarations and their proofs were moved unchanged from
[the rigidified tensor-unit module](../Picard/RigidifiedTensorUnit.md)
so both that module and [pullback tensor-unit coherence](PullbackTensorUnitProofs.md)
reuse them at the scheme-module layer. The presheaf monoidal instance is
local and explicitly named. No new mathematical result or extra hypothesis
is introduced by this reorganization. The proofs use the published
[explicit tensor construction](Tensor.md) and Mathlib's presheaf monoidal
laws; they make no independent literature claim.
