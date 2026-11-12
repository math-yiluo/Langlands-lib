# Valuative existence for the chosen dual parameter scheme

Worker 2093 wrote this derived composition for task
`54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`.
The theorem
`Langlands.AbelianScheme.relativeDualSchemeValuativeExistence`
has exactly the type
`Langlands.AbelianScheme.RelativeDualSchemeValuativeExistenceStatement.{u}`,
with no additional outer premise.

The Lean body applies
`relativeDualSchemeValuativeExistenceReduction.{u}` to
`picardZeroValuativeExtension.{u}`. The former takes
`PicardZeroValuativeExtensionStatement.{u}` as its sole input; the latter
proves that input. Both are instantiated at the same arbitrary universe `u`.
Their companion files explain the component proofs.

For an arbitrary valuative square, the reduction pulls the actual Poincare
class back along the generic map. The extension theorem extends this actual
rigidified Picard-zero class across a dominating valuation domain after a
field extension. Classification of the extension and compatibility with
actual pullback give a compatible morphism from that dominating ring's
spectrum to the chosen dual. The reduction then uses specialization in the
original square's fibre product and a stalk construction to recover a lift
over the original valuation domain `R` and its supplied fraction field `K`.
Both original triangle equations hold. The auxiliary ring and field
extensions occur only inside this construction.

The resulting statement concerns the existing `dualScheme A hA` for every
quasi-separated base `S`, abelian scheme `A / S`, and
`hA : HasDualScheme A`. It retains arbitrary-rank valuation domains and
arbitrary universe `u`. It adds no assumption about properness,
quasi-compactness, separatedness, finite type, or quasi-separatedness of the
chosen dual. It constructs no dual and uses no downstream dual geometry
assertion. The target and its imported definitions are unchanged.

This module composes the two named proofs; it does not make an additional
comparison with a source Picard functor or claim a new original-source
theorem.
