# The transfer equation from norm compatibility: proof

The module `Langlands.ClassFieldTheory.Local.NYLL.NormTransferReductionProof`
proves the published proposition
`Langlands.LocalClassField.NYLL.NormCompatibleTransferStatement` with the
theorem

```lean
theorem Langlands.LocalClassField.NYLL.normCompatibleTransfer :
    NormCompatibleTransferStatement.{u, v, w}
```

Its type is exactly the published target, with independent universe
parameters `u`, `v`, `w`. The module imports only the target's module
[`NormTransferReductionStatement`](NormTransferReductionStatement.lean). It
changes neither that statement nor anything it imports.

## What is proved

The theorem proves exactly the target statement, which is described in
[`NormTransferReductionStatement.md`](NormTransferReductionStatement.md).
Fix a prime `p` and fields `F : PadicField.{u} p`, `E : PadicField.{v} p`,
`L : PadicField.{w} p`. Assume all the binders of the host proposition
`Langlands.LocalClassField.FiniteAbelianNormTransfer`, with arbitrary supplied
`TF : F.TopologicalData` and `TE : E.TopologicalData`. Take **any** pair of
continuous multiplicative equivalences

- `rF : Fˣ ⧸ range (Units.map (Algebra.norm F (S := L))) ≃ₜ* Gal(L/F)`,
- `rE : Eˣ ⧸ range (Units.map (Algebra.norm E (S := L))) ≃ₜ* Gal(L/E)`.

Suppose the pair satisfies the norm clause: for all `b : Eˣ`,

`rF [N_{E/F}(b)] = (rE [b]).restrictScalars F`.

Then the pair satisfies the transfer clause: for all `a : Fˣ`,

`(rE [a_E]).restrictScalars F = (rF [a]) ^ Module.finrank F E`.

Here `N_{E/F}` is `Units.map (Algebra.norm F (S := E))`, `a_E` is
`Units.map (algebraMap F E).toMonoidHom a`, and `[·]` is `QuotientGroup.mk`.

The theorem is only this implication about a given pair. It does not construct
any reciprocity map or assume that one exists. It does not prove or assume the
norm clause for any particular pair.

## Implemented proof

The proof introduces the binders. Then it installs `TF.topology` and
`TE.topology` with `let`, as the statement does with `letI`. Finally it
introduces `rF`, `rE`, the norm hypothesis `hnorm` and `a : Fˣ`. Write
`n = Module.finrank F E`.

1. `rw [← hnorm]` rewrites the left side `(rE [a_E]).restrictScalars F` to
   `rF [N_{E/F}(a_E)]`. This is the norm clause at `b = a_E`, and it is the
   only use of `hnorm`.
2. `rw [← map_pow]` rewrites the right side `(rF [a]) ^ n` to
   `rF ([a] ^ n)`, because `rF` is a multiplicative equivalence. Then
   `rw [← QuotientGroup.mk_pow]` turns this into `rF [a ^ n]`, because the
   quotient projection is a monoid homomorphism.
3. `congr 2` removes `rF` and `QuotientGroup.mk` from both sides. The
   remaining goal is the equality of units `N_{E/F}(a_E) = a ^ n` in `Fˣ`.
4. `apply Units.ext` reduces this to the equality of the underlying elements
   of `F`. `simp [Algebra.norm_algebraMap]` unfolds the coercions of
   `Units.map` and of the power, which gives
   `Algebra.norm F (algebraMap F E a) = a ^ n`, and then closes the goal. The Mathlib lemma
   `Algebra.norm_algebraMap` states
   `Algebra.norm R (algebraMap R S x) = x ^ Module.finrank R S` under
   `[Module.Free R S]`. Lean finds `Module.Free F E` automatically because
   `F` is a field.

The proof uses only `hnorm`, the multiplicativity of `rF` and of the quotient
projection, and `Algebra.norm_algebraMap`. It makes no explicit use of
`IsAbelianGalois F L`, the scalar towers, continuity, bijectivity, or `TF` and
`TE`, apart from installing their topologies. The remaining binders are
available only to Lean's instance resolution.

A development `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the module with no errors or
warnings. That check reported only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Mathematical content

The proof rests on one elementary identity. If `E/F` is a field extension and
`a ∈ F`, then `N_{E/F}(a) = a^{[E:F]}`. This identity is used through Mathlib;
the proof adds no reading of any source. The theorem says nothing about
cohomological transfer and makes no comparison with
`geometricReciprocityOfCup`.

## Intended use

With universes `0, 0, 0`, this theorem gives the transfer clause of
`Langlands.LocalClassField.NYLL.FiniteAbelianNormTransferTypeZeroStatement`
(that is, `FiniteAbelianNormTransfer.{0, 0, 0}`) for any witness pair that
already satisfies the norm clause. No new witness is chosen. This is the
intermediate step requested by task `c2ca33aa-ddca-45f6-a0d6-01cfd7e677a3`
(NYLL finite reciprocity 4c). The theorem does not prove that host statement
or its norm clause.

## Environment and attribution

The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` (approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`). Worker 925 drafted the Lean proof
for task `c2ca33aa-ddca-45f6-a0d6-01cfd7e677a3`. Worker 56 submitted it for
task `7614717c-8238-4f47-937b-7c45f2379ac3`, recompiled it, and wrote this
description. Worker 7 authored the target statement in the previous instance.
