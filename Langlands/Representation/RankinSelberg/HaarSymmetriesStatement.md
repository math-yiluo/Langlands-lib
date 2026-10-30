# Symmetries of normalized general linear Haar measure

`Langlands.RankinSelberg.GeneralLinearHaarSymmetriesStatement F n` is a
proposition about the existing `generalLinearHaar F n`. It is proved by
`Langlands.RankinSelberg.generalLinearHaarSymmetries`; see the final section
and [HaarSymmetriesProof](HaarSymmetriesProof.md). Its field
`F : Type uF` has a field structure, a valuative relation, a topology, and
`IsNonarchimedeanLocalField F`. It accepts every natural number `n`, so the
matrix rank `n + 1` is positive and includes rank one. The only measurable
structure assumed is a Borel measurable structure on the actual matrix group
`G = Matrix.GeneralLinearGroup (Fin (n + 1)) F`. No characteristic,
countability, or extra unimodularity assumption is added.

Writing `μ = generalLinearHaar F n`, the four conjuncts assert:

1. `Measure.IsInvInvariant μ`, that is, the pushforward of `μ` by group
   inversion equals `μ`.
2. `MeasurePreserving (GeneralLinear.inverseTranspose (n + 1) F) μ μ`:
   the actual automorphism `g ↦ (g⁻¹)ᵀ` is measurable and its pushforward
   leaves `μ` unchanged.
3. `MeasurePreserving (fun g => GeneralLinear.inverseTranspose (n + 1) F g⁻¹)
   μ μ`: the composition `g ↦ ((g⁻¹)⁻¹)ᵀ = gᵀ` preserves `μ`.
4. For every `a : G`, the actual conjugation map `g ↦ a * g * a⁻¹`
   preserves `μ`.

The measure is precisely the published left Haar measure assigning mass one
to `Conductor.integralSubgroup (ValuativeRel.valuation F).integer n`, the
matrices whose entries and inverse entries are integral. The statement
retains that normalization; it does not introduce another measure. The
transpose clause is written using the published inverse-transpose map and
group inversion, without a separate transpose construction.

## Provenance and intended use

This is an internal derived statement for the distribution-character route
to the generic contragredient theorem. It is not attributed as a verbatim
result of an external source. The mathematical justification, implemented
by the separate proof module, is regular Haar uniqueness together with the
published `generalLinearHaar_isMulRightInvariant`. Inversion carries a
right-invariant measure to a left-invariant one; inverse transpose is a
continuous group automorphism. Both preserve the integral subgroup, which forces their Haar
scalar factors to be one. Transpose then follows by composition, and
conjugation by left and right translation invariance. The relevant existing
modules are `RankinSelberg.Measures`, `RankinSelberg.GeneralLinearUnimodularity`,
`Conductor.Congruence`, and `Group.GL.Maps`; the generic uniqueness theorem
is in pinned Mathlib's `MeasureTheory/Measure/Haar/Unique.lean`.

The proposition supplies a measure-theoretic prerequisite only. It asserts
no invariance theorem for arbitrary distributions, character separation,
trace identity, representation equivalence, or generic contragredient
realization. No proof of the proposition is included in this statement unit.

## Proof in the Library

The theorem `Langlands.RankinSelberg.generalLinearHaarSymmetries` has type

```lean
(F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)
  [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
  GeneralLinearHaarSymmetriesStatement F n
```

for an arbitrary universe `uF`. It therefore proves all four conjuncts,
inversion, inverse transpose, transpose and conjugation invariance, for every
rank `n + 1`, under exactly the assumptions listed above. Its type adds no
characteristic, countability or unimodularity hypothesis.
