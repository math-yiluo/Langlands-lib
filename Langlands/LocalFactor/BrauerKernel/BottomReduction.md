# Reduction of the Brauer kernel identity to the bottom field

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. The kernel statement
concerns actual relations over every intermediate field `E` of the common closure of `F`.
This unit shows that it suffices to treat relations over the bottom field
`Correspondence.baseExtension F`. It needs the normalized reciprocity premise and nothing
else. The global argument then only has to handle the bottom field of each p-adic field,
where the standalone transports of `BrauerKernel.StandaloneBridge` apply directly.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`, with independent universes `uF`
and `uV`.

## Statements

- `Generator.toBottom F g` (definition): for a generator `g = (L, χ, χ')` over `E`, the same
  field and characters regarded as a generator over the bottom field, with inclusion
  `baseExtension_le F L`.
- `presentationMap_mapDomain_toBottom`: if `presentationMap F e E z = 0`, then
  `presentationMap F e ⊥ (z.mapDomain (Generator.toBottom F)) = 0`. Each bottom-field
  generator class is the induction to `⊥` of the class over `E`, by the published
  `CommonClosure.induce_trans`. So the bottom-field presentation of `z` is the induction to `⊥`
  of the presentation over `E`, which is zero.
- `generatorValue_toBottom`: the generator value of `Generator.toBottom F g` for an additive
  character `ψ` of `⊥` equals the generator value of `g` for `ψ ∘ Tr_{E/⊥}`. The trace
  characters agree by the published `traceCharacter_trans`.
- `evaluationMap_eq_zero_of_bottom`: let `e` be normalized. Suppose the evaluation of every
  actual relation over the bottom field vanishes for every additive character and Haar
  family. Then for every `E`, `ψ`, Haar family and actual relation `z` over `E`,
  `evaluationMap F E ψ measures z = 0`.

## Proof of the reduction

The published `padicUnitaryAdditiveCharacterExists` gives a nontrivial additive character
`ψ₀` of the bottom field. The accepted `evaluationMap_additiveCharacter_independent` of
`BrauerKernel.Determinant` replaces `ψ` by `ψ₀ ∘ Tr_{E/⊥}`. By
`Finsupp.linearCombination_mapDomain` and `generatorValue_toBottom`, the evaluation over `E`
for this character is the evaluation over `⊥` of `z.mapDomain (Generator.toBottom F)` for
`ψ₀`. That is an actual relation by `presentationMap_mapDomain_toBottom`, so the hypothesis
makes it vanish.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, Lemma 4.7 (printed
page 540, PDF page 40). There the criterion for a theory of constants on `K'/K` is stated over
the base field `K` alone. Axiom (3) transports degree-zero relations of subgroups by
induction. The reduction here is the common-closure counterpart: induction from `E` to the
bottom field with the trace character `ψ ∘ Tr`. It is internal bookkeeping that uses the
published coherence of induction and trace pullback and the accepted additive-character
independence.
