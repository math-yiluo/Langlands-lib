# Arithmetic transport commutes with the CM involutions

Module `Langlands.Global.CMConjugationArithmeticTransport` (namespace
`Langlands.Global.CMConjugation`). Proved lemmas only; no new definitions.

## Setting

For a CM field `E`, `fieldConj E` is the CM involution `IsCMField.complexConj E` of
Mathlib as a ring automorphism, and the module `Langlands.Global.CMConjugationGL`
defines its entrywise actions: `finiteConj` on the finite adelic matrix group,
`infiniteConj` on the infinite adelic matrix group, `compactConj` on the standard compact
subgroup at infinity, `mixedConj` (complex conjugation of the complex coordinates) on the
mixed archimedean coordinates, and `lieConj` on the real matrix Lie algebra. For a ring
isomorphism `e : K ≃+* L` of number fields the modules `Langlands.Global.AdelicGLTransport`,
`Langlands.Global.ArchimedeanCompactTransport`, `Langlands.Global.ArchimedeanGLTransport`
and `Langlands.Global.ArchimedeanLieTransport` define the arithmetic transports
`finiteEquiv n e`, `infiniteEquiv n e`, `compactEquiv n e`, `mixedEquiv e` and
`realLieEquiv n e`. The fields `K : Type uK` and `L : Type uL` have independent
universes.

## Results

- `mixedEquiv_fieldConj E x : mixedEquiv (fieldConj E) x = mixedConj E x`, for one CM
  field `E`. Transport of the mixed coordinates along the CM involution is entrywise
  complex conjugation. Proof: `mixedEquiv (fieldConj E)` is
  `ringEquiv_mixedSpace E ∘ infiniteComplexConj ∘ (ringEquiv_mixedSpace E)⁻¹`, and the
  published `mixedSpace_infiniteComplexConj` identifies
  `ringEquiv_mixedSpace E ∘ infiniteComplexConj` with
  `mixedConj E ∘ ringEquiv_mixedSpace E`.

For CM fields `K`, `L` and a ring isomorphism `e : K ≃+* L`:

- `ringEquiv_complexConj e x : e (complexConj K x) = complexConj L (e x)`. Proof: choose
  a complex embedding `ψ : L →+* ℂ`. Mathlib's `IsCMField.complexEmbedding_complexConj`
  says that the CM involution induces complex conjugation under every complex
  embedding. Applied to the embedding `ψ ∘ e` of `K` it gives
  `ψ (e (complexConj K x)) = conj (ψ (e x))`, and applied to `ψ` it gives
  `ψ (complexConj L (e x)) = conj (ψ (e x))`. Since `ψ` is injective, the two arguments
  agree. This is the uniqueness of the CM involution under complex embeddings, read
  through `e`.
- `fieldConj_trans e : (fieldConj K).trans e = e.trans (fieldConj L)`, the same identity
  for ring isomorphisms.
- `finiteEquiv_finiteConj n e d :
  finiteEquiv n e (finiteConj K n d) = finiteConj L n (finiteEquiv n e d)`, and
  `infiniteEquiv_infiniteConj n e g`, the same identity for `infiniteEquiv` and
  `infiniteConj`. Proof: entrywise, both sides are the transports of the matrix entry
  along `(fieldConj K).trans e` and along `e.trans (fieldConj L)`. The published laws
  `finiteAdeleEquiv_trans` and `infiniteAdeleEquiv_trans` (modules
  `Langlands.Global.AdelicFunctoriality.Finite` and
  `Langlands.Global.AdelicFunctoriality.Infinite`) turn composites of field isomorphisms into
  composites of adele transports, and `fieldConj_trans` identifies the two composites.
- `compactEquiv_compactConj n e k :
  compactEquiv n e (compactConj K n k) = compactConj L n (compactEquiv n e k)`: the
  underlying identity of infinite adelic matrices is `infiniteEquiv_infiniteConj`.
- `mixedEquiv_mixedConj e x : mixedEquiv e (mixedConj K x) = mixedConj L (mixedEquiv e x)`.
  Proof: rewrite both conjugations with `mixedEquiv_fieldConj`, combine the transports
  with `ArchimedeanLieTransport.mixedEquiv_trans`, and apply `fieldConj_trans`.
- `realLieEquiv_lieConj n e X :
  realLieEquiv n e (lieConj K n X) = lieConj L n (realLieEquiv n e X)`. Proof: both maps
  act entrywise on the underlying mixed matrices (`realLieEquiv_entry`, `lieConj_apply`),
  so this is `mixedEquiv_mixedConj` entry by entry.

## Provenance

These are internal compatibility lemmas. The only arithmetic input is that the CM
involution of a CM field is the automorphism inducing complex conjugation under every
complex embedding (Mathlib, `Mathlib/NumberTheory/NumberField/CMField.lean`,
`IsCMField.complexEmbedding_complexConj`). The module
`Langlands.Automorphic.ConjugateContragredientArithmeticTransport` uses them to pull back
conjugate-contragredient pairings along arithmetic transport.
