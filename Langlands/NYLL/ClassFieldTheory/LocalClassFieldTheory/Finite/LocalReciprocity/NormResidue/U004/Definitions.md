# Topological abelianization of a finite abelian Galois group

`Langlands.NYLL.LocalClassFieldTheory.topologicalAbelianizationEquivSelf`
constructs

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsAbelianGalois K L] :
TopologicalAbelianization Gal(L / K) ≃ₜ* Gal(L / K)
```

Both fields remain in universe zero. The automorphism group carries its native
Krull topology. The construction first uses the inverse of the published
`Langlands.NYLL.LocalClassFieldTheory.topologicalAbelianization_finite_equiv`
and then the inverse of Mathlib's `Abelianization.equivOfComm`. The quotient's
local discrete-topology instance and the finite Krull group's discreteness
make both directions continuous by `continuous_of_discreteTopology`.
This is an actual continuous multiplicative equivalence. It introduces no global
instance and does not construct an Artin map.

## Source correspondence and changes

M258.004 at original `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean`,
lines 62–74 (definition at line 64), maps
`LocalClassFieldTheory.topologicalAbelianizationEquivSelf` to the public name above.
The original file SHA-256 is
`60e337f31f50475238854446e8e560075822e99847b41110890a91d9c46f38cd`.

The definition body and complete source section telescope are unchanged. The
namespace gains `Langlands.NYLL`; the unused `open LocalFieldTheory` is omitted.
The full source TopologicalReciprocity import is replaced by its published
`TopologicalReciprocity.U010.Definitions` module. The original two Mathlib
imports and `IsMulCommutative` scope remain. The module prose is focused on this
unit. The source's valuation, base-field topology and local-field section
instances are unused and vanish on elaboration in this extraction, as in the
original; no local-field assumption is replaced by an extra premise.

Focused compilation with these imports succeeds. A private full-signature
check (`a620416a-041d-49b1-9545-b758efc26225`) confirms exactly the displayed
telescope and no universe parameters. Thus M258.001–003 and the earlier Artin
construction are not dependencies of this unit. The M257.009 Mathlib replacement
is documented in the imported U010 pair. Other M258 units remain separate.

## Attribution

The source is Naganori Yamaguchi's ClassFieldTheory, assisted by OpenAI Codex,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The original copyright and author header is retained. The explicit modification
record credits Worker 120 (10 November 2026). The unchanged Apache-2.0 files are
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
No file-specific NOTICE entry or patch10 change applies to this unit.
