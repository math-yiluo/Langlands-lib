# The unitary norm theorem from embeddings of unitary tori

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormReduction`.

`Langlands.CentralSimple.NumberFieldUnitaryNormReductionStatement.{u}` is the implication

```text
NumberFieldUnitaryEmbeddingStatement → NumberFieldUnitaryNormTorusStatement →
  NumberFieldUnitaryNormStatement
```

in one universe `u`. The three propositions are stated in
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingStatement`,
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormTorusStatement` and
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormStatement`; this module does not prove
the two premises. The theorem `Langlands.CentralSimple.numberFieldUnitaryNormReduction`
proves the implication.

## Proof

Let `F`, `E`, `B`, `τ` and `z` satisfy the hypotheses of the unitary norm theorem. They are
exactly the hypotheses of `NumberFieldUnitaryNormTorusStatement`, which gives a field `P`
with `Module.finrank E B = Module.finrank E P ^ 2`, an involution `σ` of `P` acting on `E` by
conjugation, an element `x ∈ P` with `x σ(x) = 1` and `Algebra.norm E x = z`, and local
embeddings of `(P, σ)` into `(B, τ)` at every place. These are the hypotheses of
`NumberFieldUnitaryEmbeddingStatement`, which gives an `E`-algebra homomorphism
`φ : P →ₐ[E] B` with `φ (σ p) = τ (φ p)`.

The element `x` is nonzero, since `x σ(x) = 1`, so it is a unit of the field `P` and `φ x` is
a unit of `B` (the image of `Units.mk0 x` under `Units.map φ`). It is unitary:
`φ x * τ (φ x) = φ x * φ (σ x) = φ (x σ(x)) = 1`. The reduced degree
`reducedDegree E B = Nat.sqrt (Module.finrank E B)` equals `Module.finrank E P` by
`Nat.sqrt_eq'`. So `Langlands.CentralSimple.reducedNorm_eq_field_norm` (module
`Langlands.Algebra.ReducedNormSubfield`), which identifies the reduced norm of an element of
a subfield of reduced degree with its field norm, gives
`reducedNorm E B E (1 ⊗ φ x) = Algebra.norm E x = z`.

## Provenance

This is the final step of the proof of Theorem 6.28 in Platonov and Rapinchuk, *Algebraic
Groups and Number Theory* (1994), §6.7, printed p. 366 (PDF p. 376), source
`platonov-rapinchuk-1994-algebraic-groups-number-theory`: "It remains to show there is an
`L`-embedding `θ : P → A` as an algebra with involution, since then `θ(x)` will be the desired
element." The same step is the remark after Step 3 of the plan in Kneser, *Lectures on Galois
Cohomology of Classical Groups* (1969), §5.6, printed p. 78 (PDF p. 84), source
`kneser-1969-galois-cohomology-classical-groups`: since the embedded algebra has dimension
`n`, its norm is the reduced norm.
