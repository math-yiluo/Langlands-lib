# Right-invariant Haar from a compact discrete quotient

`Langlands.Global.compactDiscreteQuotientHaarRightInvariant.{u}` proves
exactly
`Langlands.Global.CompactDiscreteQuotientHaarRightInvariantStatement.{u}`.
For every locally compact Polish topological group `H : Type u` with its
Borel measurable structure, and every discrete subgroup `Γ` whose actual
left quotient `LeftCosetSpace Γ` is compact, the actual ambient measure
`Measure.haar` is right invariant. The subgroup need not be normal.

The proof uses the published strict Borel fundamental domain
`LeftCosetSpace.fundamentalDomain Γ hΓ`. Second countability, supplied by
Polishness, makes `Γ` countable. The actual quotient measure
`LeftCosetSpace.haarQuotientMeasure Γ hΓ` is locally finite and nonzero.
Compactness makes it finite, and its total mass equals the ambient Haar
mass of the chosen domain. Consequently that domain has finite nonzero
Haar mass; this is a conclusion of the hypotheses, rather than a supplied
finite-volume premise.

For each `g : H`, the preimage of the domain under `x ↦ x * g` is
measurable and is another strict fundamental domain. Associativity
transfers the pointwise unique representative property from `x * g` to
`x`. Equality of fundamental-domain masses for the left subgroup action
therefore gives the same Haar mass to the original domain and this right
preimage.

Mathlib's `Measure.map_right_mul_eq_modularCharacterFun_smul` expresses
the right-translation pushforward of Haar as
`Measure.modularCharacterFun g • Measure.haar`. Evaluating it on the
domain and using the mass equality shows that the modular factor times
the finite nonzero domain mass equals that mass. Cancellation in
`ℝ≥0∞` makes the factor one. Substitution in the measure identity proves
right invariance for every `g`.

This is an internal analytic argument using the published strict-domain
and quotient-measure constructions and the pinned Mathlib modular
scaling theorem. It supplies the compact discrete quotient prerequisite
for the parent automorphic construction. General reductive and norm-one
adelic unimodularity remain separate obligations.

Worker 94 authored the complete Lean proof in parent shared draft
revision 2. Worker 1643 adopted that proof unchanged and prepared its
paired explanation and submission. Both are actual coauthors.
