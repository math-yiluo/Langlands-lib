# An upper bound for finite residue-field projective dimension

`Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionUpperBoundStatement.{u}`
asserts that for every Noetherian local commutative ring `R : Type u`,

```lean
(∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE
  (ModuleCat.of R (IsLocalRing.ResidueField R)) n) →
CategoryTheory.projectiveDimension
  (ModuleCat.of R (IsLocalRing.ResidueField R)) ≤ ringKrullDim R
```

The premise says that the canonical residue-field module has finite
projective dimension in Mathlib's categorical, Ext-based sense. By
`CategoryTheory.projectiveDimension_ne_top_iff`, it is equivalent to
that dimension being different from `⊤`. The conclusion compares the
actual projective dimension with the Krull dimension in `WithBot ℕ∞`.
It does not assert that every chosen upper bound `n` is at most the Krull
dimension: such an assertion would be false for unnecessarily large bounds.

The universe is arbitrary. There is no domain, dimension, characteristic,
completeness or regularity hypothesis, and no hypothesis on the projective
dimension of other finite modules. The Lean file only defines the proposition.

## Original source and role

This is Stacks Project Lemma 10.110.4,
[Tag 00OB](https://stacks.math.columbia.edu/tag/00OB), expressed using
Mathlib's projective-dimension value and a separate finiteness premise.
The complete original page and both comments are retained in `00OB.html`
of registered source
`stacks-residue-field-projective-dimension-bounds-2026-11-01`, directory
SHA-256 `40635b9a819b6011c03de10b01cecd53bb1c9e67a82d3022bfa106470bac0743`.
The complete page and its comments have been read. There is no separate
project errata note for this source. The comments concern the reference for
existence of a finite resolution by finite modules.

Together with the lower bound by embedding dimension in Tag 00OA, this
inequality is used for implication (1) to (3) of Proposition 10.110.5,
Tag 00OC. No proof is claimed here, and the statement does not assume that
regularity criterion or any localization consequence of it.
