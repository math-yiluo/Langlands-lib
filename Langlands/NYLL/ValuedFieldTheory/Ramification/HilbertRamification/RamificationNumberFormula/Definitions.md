# Extended-natural truncation at a real bound

This module extracts exactly NYLL source unit M313.004:
`RamificationTheory.HilbertRamification.Higher.truncateENatAtDVF`,
from Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationNumberFormula.lean`,
lines 49–50 (docstring at line 48).

The adapted declaration is
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.truncateENatAtDVF`.
Its complete interface and defining expression are:

```lean
noncomputable def truncateENatAtDVF (i : ℕ∞) (r : ℝ) : ℝ :=
  ENat.recTopCoe r (fun n => min (n : ℝ) r) i
```

Mathlib's `ENat.recTopCoe` sends the infinite input `⊤` to the first branch
`r`, and a finite input `(n : ℕ∞)` to `min (n : ℝ) r`. Thus the result
truncates an extended natural depth at a real bound. The bound is any real
number, including a negative one; there is no nonnegativity premise.

Both arguments are explicit, in the source order, and there are no implicit
arguments, instance arguments or universe parameters. The fields, valuations,
finite-dimensionality, Galois and residue-separability assumptions in the
surrounding source section do not occur in this declaration. Its three local
finite-group and decidability instances are likewise unused.

## Source correspondence and modifications

The namespace gains the `Langlands.NYLL` prefix. The defining expression and
original docstring are retained verbatim. The source `noncomputable section`
is retained, since the minimum uses Mathlib's noncomputable real linear order.
Unused source section variables, universe declarations and local instances
are omitted.

The source's whole-module imports are replaced by
`Mathlib.Data.ENat.Defs`, supplying `ℕ∞` and `ENat.recTopCoe`, and
`Mathlib.Basic.Real.Basic`, supplying `ℝ`, natural-number casts and its order.
The latter is the current nondeprecated location in the approved Mathlib pin.
These imports supply the actual Mathlib types and operations directly.
Searches of Library NYLL/AnthropicFLT and relevant Mathlib extended-natural,
valuation and ramification sources found no existing named construction with
this interface and body.

This unit adds only the data definition. The three elementary identities at
source lines 53–72 and the ramification-number sum formula are separate work.
The definition requires no intrinsic-ramification-number or monogeneity input.

## Source, license and authorship

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its readable root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
followed by the original source path above. No matching NYLL erratum was
found in the supplied Library's `notes/errata/`.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). Apache-2.0 applies. The existing
[`licenses/NYLL/LICENSE`](../../../../../../licenses/NYLL/LICENSE) and
[`licenses/NYLL/NOTICE`](../../../../../../licenses/NYLL/NOTICE) are retained
unchanged and match the pinned originals. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 544 extracted this unit and documented the modifications on
14 November 2026.

The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, environment artifact
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
