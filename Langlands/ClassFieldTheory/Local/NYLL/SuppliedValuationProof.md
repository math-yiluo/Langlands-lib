# Relative valuation extension for arbitrary supplied local-field data

Worker 537 authored the proof and this explanation. Worker 66 specified the
interface and the proof route in the task. The imported statement by Worker 104
and integer-membership comparison by Worker 90 retain their original authorship.

The module `Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationProof`
proves `Langlands.LocalClassField.NYLL.suppliedRelativeValuationExtension`.
Its type is exactly the published proposition
`Langlands.LocalClassField.NYLL.SuppliedRelativeValuationExtensionStatement.{u,v}`,
with independent field universes `u` and `v`.

For every prime `p`, the proposition takes fields `F : PadicField.{u} p` and
`E : PadicField.{v} p`, the given `Algebra F.Carrier E.Carrier`, its certificate
`IsScalarTower (Padic p) F.Carrier E.Carrier`, and arbitrary supplied
`TF : F.TopologicalData` and `TE : E.TopologicalData`. The proof installs
exactly `TF.valuativeRel` followed by `TE.valuativeRel` as local instances.
It constructs

```lean
Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
  (ValuativeRel.valuation E.Carrier)
```

along this actual relative algebra map.

The proof fills the sole field of `Valuation.HasExtension`, equivalence of the
base valuation with the extension valuation comapped along
`algebraMap F.Carrier E.Carrier`. Mathlib's
`Valuation.isEquiv_iff_val_le_one` reduces this to an equivalence of the two
value-at-most-one conditions for each element of `F.Carrier`. The existing
`Langlands.PadicField.TopologicalData.relative_mem_integers_iff TF TE x`
states that the image is in `TE.Integers` if and only if the original element
is in `TF.Integers`. Reversing that equivalence and simplifying
`TopologicalData.Integers`, `Valuation.mem_integer_iff`, and
`Valuation.comap_apply` supplies the required condition.

This is an internal derived result from the published supplied-data
integer-membership comparison in `Langlands.LocalField.RelativeIntegers`
and the pinned Mathlib valuation API. The proof reuses that comparison directly;
it makes no new original-literature claim. Valuation equivalence compares the
valuation order relations. It does not assert numerical equality between
independently normalized valuations.

The theorem adds no global instance or integer/residue map. Its conclusion is
only the supplied relative valuation bridge. Reciprocity, norm/transfer,
compatible uniformity, integral closure, class formation, and comparison with
`geometricReciprocityOfCup` remain separate obligations.

The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
