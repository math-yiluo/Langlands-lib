# Supplied residue congruence

Worker 542 authors this internal, derived proof of the published
`Langlands.LocalClassField.NYLL.SuppliedResidueCongruenceStatement.{u}`.
The theorem is `Langlands.LocalClassField.NYLL.suppliedResidueCongruence.{u}`;
its complete type is that exact proposition. The carrier universe remains
arbitrary. The sole import is
[`SuppliedResidueStatement`](SuppliedResidueStatement.md), whose imported
normalization definitions supply every ring, map and valuation used here.

The resulting equivalence is

```text
T.residue x = T.residue y ↔
  T.discreteValuation ((x : F.Carrier) - (y : F.Carrier)) < 1.
```

For arbitrary prime `p`, `F : Langlands.PadicField.{u} p`,
`T : F.TopologicalData` and `x y : T.Integers`, the proof rewrites residue
equality as residue zero of `x - y`, using `sub_eq_zero` and `map_sub`.
`IsLocalRing.residue_eq_zero_iff` identifies membership in the maximal ideal
of the actual supplied integer ring. `IsLocalRing.mem_maximalIdeal`
identifies that membership with being a nonunit, and
`Valuation.Integer.not_isUnit_iff_valuation_lt_one` identifies nonunits
with elements whose supplied valuation is strictly below one. The subtype
coercion of `x - y` is definitionally the field difference.

The supplied discrete valuation composes that valuation with
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier`. The
isomorphism preserves one (`map_one`) and reflects strict inequalities
(`e.strictMono.lt_iff_lt`), giving both directions of the desired
equivalence. These criteria apply also when `x = y`: the residue difference
is zero and the valuation difference is zero, strictly below one.
No nonzero hypothesis or separate zero exclusion is used.

The proof uses only local instances taken from `T`. It introduces no
replacement ring, valuation, residue map, or additional compatibility premise.
Its provenance is the existing Library constructions and the pinned Mathlib
quotient and valuation interfaces, rather than an external proof.
The inspected Mathlib interfaces are from commit
`5ed2965256430c3649e86755f9576b54eca72435`; the approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0.

Later consumers can apply the theorem to `z` and `x ^ q`, then use `map_pow`
and the coercion law for powers. This converts
`T.residue z = (T.residue x) ^ q` into
`T.discreteValuation ((z : F.Carrier) - (x : F.Carrier) ^ q) < 1`.
No Artin map, unramifiedness hypothesis, Artin action or normalization
theorem enters this comparison.
