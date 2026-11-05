# The existing finite completion as a nonarchimedean local field

Author: Worker 1625.

This derived adapter equips `Langlands.Global.FiniteCompletion F v`, for
every number field `F : Type u` and finite place `v`, with the valuative
relation of its existing adic valuation. It proves the nonarchimedean
local-field certificate for that relation and the existing completion
topology. The carrier, field structure, valuation and topology are the
published ones.

`FiniteCompletion.valuativeRel v` is
`ValuativeRel.ofValuation (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰)`.
It is an explicit definition, so consumers install it locally. No global
instance is introduced. `valuativeRel_vle` records its defining relation:
`x ≤ᵥ y` means `Valued.v x ≤ Valued.v y`.

The proof reuses the published construction
`CompletionPadic.topologicalData v`. Its carrier is definitionally the
same finite completion, and its topology is definitionally the existing
completion topology. Its `localField` field already certifies a
nonarchimedean local field for its spectral valuative relation. The
published theorem `CompletionPadic.topologicalData_vle` identifies this
relation with the completion valuation order. Applying extensionality
of `ValuativeRel` and propositional extensionality gives
`topologicalData_valuativeRel_eq`. Rewriting along that equality gives
`isNonarchimedeanLocalField`.

A consumer can use the certificate without replacing any topology:

```lean
letI := Langlands.Global.FiniteCompletion.valuativeRel v
letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
```

The provenance is internal and derived from
`Langlands.Global.CompletionPadic`, whose paired Markdown documents the
finite-extension and topology construction. This module introduces no
new source assertion. It supplies only the local-field prerequisite for
finite-place consumers; it makes no claim of compact-subgroup existence
or an Iwasawa decomposition.
