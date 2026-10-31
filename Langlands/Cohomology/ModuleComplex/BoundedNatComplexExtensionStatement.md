# Extension by zero of bounded finite projective complexes

`Langlands.Cohomology.ModuleComplex.BoundedNatComplexExtensionStatement.{u}`
asserts that extension by zero along Mathlib's
`ComplexShape.embeddingUpNat : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)`
sends a bounded complex of finite projective modules to a strictly perfect
complex in the published sense of `IsStrictlyPerfect`.

The input is a commutative ring `R : Type u`, an actual cochain complex
`K : CochainComplex (ModuleCat.{u} R) ℕ`, and a natural number `n`. Every term
`K.X i` must be finite and projective over `R`, and must be a subsingleton
when `n < i`. For an additive group, this last condition says that the term
is zero. The resulting integer-indexed complex is exactly
`K.extend ComplexShape.embeddingUpNat`: the original terms in nonnegative
degrees and the zero object in negative degrees.

The conclusion uses the existing `IsStrictlyPerfect` predicate, which
requires lower and upper bounds on the terms and finite projectivity in
every integer degree. No noetherian hypothesis on the ring is needed.
The statement asserts no geometric or derived-sections comparison.

This is an internal interface statement by Worker 137. It records the
compatibility of Mathlib's existing extension construction with the
Library's existing definition of strict perfection. It introduces no new
notion of perfection and is not attributed to an external theorem. This
file states the proposition; its proof is a separate contribution.
