# Surjectivity of the normalized valuation modulo a degree

The theorem
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree_surjective`
has exactly the published proposition type
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree_surjectiveStatement`.
It retains the arbitrary universe `u`, the field `K : Type u`, and the
instances `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`. Every natural degree `n` is covered,
including zero; no positivity or `NeZero` instance is added.

The map being proved surjective is the existing
`valuationModDegree K n : Additive Kˣ →+ ZMod n`. It is the composite of
the published integer-valued normalized valuation `valuationMap K` and
integer reduction into `ZMod n`. Its definition, its sign convention,
and its imported data are used unchanged.

## Implemented proof

For `z : ZMod n`, `ZMod.intCast_surjective` provides an integer `m`
whose image is `z`. The published theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective`
then provides `x : Additive Kˣ` with `valuationMap K x = m`.
Definitional evaluation of the composite `valuationModDegree` changes
the remaining goal to equality of these integer casts, and rewriting
by that equality closes the proof. This uses no evaluation theorem for
`valuationModDegree`, so M266.002 is not a prerequisite.

The only direct imports are the published additive statement module and
the valuation-map surjectivity proof module. The latter is the M134.005
publication owned by Task 5917
(`3d7fcc34-1816-4f9c-bde9-f992f70a4137`); its proof is not duplicated here.
The result concerns the existing NYLL normalized valuation and its reduction.

## Source correspondence and modifications

This adapts M266.003, source theorem
`LocalClassFieldTheory.valuationModDegree_surjective`, lines 44–50 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The full source file was read and has SHA-256
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable errata entry was found in the project notes.

The proof follows the source's two successive lifts. Worker 341 added the
`Langlands.NYLL` namespace prefix, replaced the explicit source telescope
in the theorem type by the exact closed Library target, and reduced the
imports to the target and the prerequisite proof. The source's last
`simp [hx]` is replaced by a `change` using definitional evaluation of
the existing composite, followed by `rw [hx]`. No new mathematical
hypothesis or auxiliary theorem is introduced.

The original copyright and author header is retained, with a modification
record. Apache-2.0 license and notices remain in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
