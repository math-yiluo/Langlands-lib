# Trivial multiplicative reduced valuation and divisibility

This module proves
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_eq_one_iff_dvd`
with type exactly the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_eq_one_iff_dvdStatement`.
The target is imported from
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.MultiplicativeStatements`.

For every `K : Type u` with `[Field K]`, `[ValuativeRel K]`,
`[TopologicalSpace K]`, and `[IsNonarchimedeanLocalField K]`, every
`n : Nat`, and every `x : Kˣ`, the theorem says that
`valuationModDegreeMulHom K n x = 1` if and only if `(n : Int)` divides
`LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)`.
The universe is arbitrary and there is no positivity or nonzero assumption on
`n`; the theorem includes `n = 0`.

The proof introduces the target's parameters and uses definitional reduction:
the multiplicatively tagged equation to one becomes the equation to zero of
the normalized integer valuation cast into `ZMod n`. It then applies
Mathlib's `ZMod.intCast_zmod_eq_zero_iff_dvd` to that integer and `n`.
The published homomorphisms, valuation map, target, and their hypotheses are
used unchanged. No auxiliary declaration or instance is introduced.

The original theorem is `LocalClassFieldTheory.valuationModDegreeMulHom_eq_one_iff_dvd`,
M266.009, lines 96–103 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Its full source-file SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the original
module path. The source header and relevant lines were read, and the file hash
was verified. No applicable source errata file was found in the project notes.

Worker 531 retained the original copyright and author header, added the
modification record and namespace prefix, and gave the theorem the exact
published closed proposition as its type. The original proof first converts
to the additive reduced-valuation equation and applies M266.004,
`valuationModDegree_eq_zero_iff_dvd`; the implemented proof unfolds that
additional layer and applies the same Mathlib divisibility criterion directly.
Only the published target module is imported, with its published data and
Mathlib dependencies. No private draft or unaccepted theorem is imported.
The Apache-2.0 license and original notices remain in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.

The focused Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module with zero errors
and zero warnings. Declaration inspection confirmed the universe parameter
`u` and only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
This is development evidence; independent review and the staged exact-target
check establish acceptance separately.
