# Surjectivity of the multiplicative valuation modulo degree

The theorem
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_surjective`
proves exactly the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_surjectiveStatement`.
It retains arbitrary `K : Type u`, the instances `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]` and every natural
modulus `n`, including zero. Its conclusion is surjectivity of the published
`valuationModDegreeMulHom K n : Kˣ →* Multiplicative (ZMod n)`.

For `z : Multiplicative (ZMod n)`, the proof applies the additive theorem
`valuationModDegree_surjective K n` to `Multiplicative.toAdd z`. It obtains
`x : Additive Kˣ` and an equation for its additive reduced valuation. The
desired witness is `Additive.toMul x`. Injectivity of `Multiplicative.toAdd`
reduces the multiplicative equality to the additive witness equation by
definitional reduction of the published map and the type tags.

The imports are the published multiplicative statement module and the
`UnramifiedNormSubgroup.U003.Proofs` additive surjectivity proof. The
valuation map, reduction and multiplicative homomorphism are imported by
their Lean names. This unit introduces no definitions or instances and
does not change the target or its imported data.

## Source correspondence

This is M266.008, source theorem
`LocalClassFieldTheory.valuationModDegreeMulHom_surjective`, lines 86–93 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete original file was read and its SHA-256 verified as
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered under `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable entry was found in the project errata notes.

Worker 226 added the namespace prefix and modification record, replaced
the original theorem telescope by the exact closed Library statement and
used focused imports. The proof follows the original tag-transport route;
the original final `simpa using hx` is replaced by `exact hx`, relying on
definitional equality. The original copyright and author header is retained.
Apache-2.0 license and notices are published in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. No other worker's draft was reused.
