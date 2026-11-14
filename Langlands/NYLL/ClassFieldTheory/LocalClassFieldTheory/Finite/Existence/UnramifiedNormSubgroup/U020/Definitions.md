# The unramified norm quotient as a valuation quotient

`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormQuotientEquivZMod`
is the multiplicative equivalence

```lean
Kˣ ⧸ unramifiedNormSubgroup K n ≃* Multiplicative (ZMod n)
```

for every `K : Type u` with `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]` and every `n : Nat`.
There is no nonzero-modulus assumption: the definition also applies to
`n = 0`. The domain uses the published subgroup of actual field units whose
normalized integer valuation is divisible by `n`.

The construction is the source composite. The published theorem
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom`
identifies the kernel of the reduced valuation with that subgroup.
`QuotientGroup.quotientMulEquivOfEq` first transports the subgroup quotient
to the kernel quotient, using the symmetric equality. Mathlib's
`QuotientGroup.quotientKerEquivOfSurjective` then identifies the kernel
quotient with the codomain of the published `valuationModDegreeMulHom K n`,
using the published theorem
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_surjective`.
These inputs are imported from `UnramifiedNormSubgroup.U018.Proofs` and
`UnramifiedNormSubgroup.U008.Proofs`. The resulting equivalence uses the
actual normalized valuation map; no extra proof hypothesis or substitute
quotient is introduced. Its computation theorem is a separate source unit.

## Source correspondence and modifications

This is M266.020, source
`LocalClassFieldTheory.unramifiedNormQuotientEquivZMod`, declaration lines
203–210 (documentation begins at line 201) of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The complete original
file was read; its SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path
above. No applicable project errata entry was found.

Worker 205 extracted this declaration, prefixed its namespace with
`Langlands.NYLL`, and replaced the original broad imports with the two
published proof modules above. Its body, arbitrary universe, section mode,
parameters and hypotheses are unchanged. It reuses the existing adaptations
by Lean name and does not copy another worker's unpublished proof. The
original copyright, Apache-2.0 notice and author header are retained with
an explicit modification record. The license and notices are published in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Development validation

Lean-service check `b2ff7528-94b8-4ae6-96b7-28a3ae0a680c` in the approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module and
inspected the exact definition with zero errors and warnings. Inspection
retains level parameter `u` and reports only `propext`, `Classical.choice`
and `Quot.sound`. This development result does not replace independent
semantic review and publication.
