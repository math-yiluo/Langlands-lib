# Degree of the embedded finite subextensions of a residue algebraic closure (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finrank_finiteResidueGaloisIntermediateFieldInStatement`
(M236.009, in `ResidueAlgebraicClosureDegree/Initial/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.finrank_finiteResidueGaloisIntermediateFieldIn`,
which carries the source's `@[simp]` attribute.

Adapted by Worker 46 (Lean port) and Worker 5163 (check and Markdown) from Naganori Yamaguchi,
ClassFieldTheory (NYLL), pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
theorem `finrank_finiteResidueGaloisIntermediateFieldIn`, lines 97–110 (`omit` line 97,
docstring 98, `@[simp]` 99, statement 100–103, proof 104–110; whole-file SHA-256
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Target

Under the source's `variable` blocks (lines 39–41) and its
`omit [Algebra.IsAlgebraic k Omega]`, the theorem takes, in order, `k : Type u`,
`[Field k]`, `[Fintype k]`, `Omega : Type v`, `[Field Omega]`, `[Algebra k Omega]`,
`[IsAlgClosed Omega]`, `n : ℕ` and `[NeZero n]`, at arbitrary universes `u` and `v`. Its type is
`finrank_finiteResidueGaloisIntermediateFieldInStatement k Omega n`. That statement is a reducible
`abbrev` for

```lean
Module.finrank k (finiteResidueGaloisIntermediateFieldIn k Omega n) = n
```

So the finite field `k` has, inside any algebraically closed field `Omega` that is a
`k`-algebra, a finite Galois intermediate field of degree `n` over `k`. Here
`finiteResidueGaloisIntermediateFieldIn k Omega n` (M236.008) is the image in `Omega` of
Mathlib's degree-`n` model `FiniteField.Extension k (ringChar k) n` under the embedding
`finiteResidueExtensionEmbeddingInto k Omega n` (M236.005), which is given by `IsAlgClosed.lift`.
Because the target is reducible, the `@[simp]` attribute registers the unfolded equation, as in the
source. A private check (not part of this module) confirmed that `simp` rewrites
`Module.finrank k (finiteResidueGaloisIntermediateFieldIn k Omega n)` to `n` with this theorem.

## Implemented proof

First the proof supplies the instance `Fact (ringChar k).Prime` with the local
`have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩`. Here `Finite k` comes
from `[Fintype k]`. This is the value of the source's private instance
`finiteResidueBaseRingCharPrime` (M236.001), which the Library does not declare. The published
Initial definitions inline the same value. It is needed to write
`FiniteField.Extension k (ringChar k) n`. Since `Fact` is a proposition, this local instance and
the one inside the definitions agree. The rest is the source proof, a two-step `calc`.

1. `(finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv.finrank_eq.symm` takes the
   `k`-algebra isomorphism M236.007 between the model `FiniteField.Extension k (ringChar k) n` and
   the embedded intermediate field, and turns it into an equality of their `Module.finrank k`. The
   `Module.finrank` of the Galois intermediate field M236.008 is by definition that of its
   underlying `finiteResidueIntermediateFieldIn k Omega n` (M236.006).
2. Mathlib's `FiniteField.finrank_extension k (ringChar k) n` shows that the model has degree `n`.

No auxiliary declaration, instance or hypothesis is added; the instance above is local to the
proof. The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Modifications

- The namespace gets the prefix `Langlands.NYLL`. The theorem's type is the published
  `Statement` instead of the restated proposition. The theorem name, the `omit` command and the
  `@[simp]` attribute are kept.
- The M236.001 instance value comes from a local `have` in the proof instead of the source's
  private section instance. The source's private instances M236.002–M236.004 are not needed and
  are not declared.
- The theorem docstring "States the theorem `finrank_finiteResidueGaloisIntermediateFieldIn`."
  becomes a sentence stating the result, and a module docstring describing these modifications
  replaces the source's module docstring.
- Imports: the published module `ResidueAlgebraicClosureDegree/Initial/Statements` (left
  unchanged) instead of the NYLL source imports. The `open` commands are those of the Initial
  modules: the source's, minus `ClassFormation` and
  `RamificationTheory.Field.absoluteGaloisGroup`, which this proof does not use.

The original copyright and author header is kept. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
