# NYLL M395.001–.002: DVR polynomial root-proximity targets

The paired module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity.Statements`
defines two closed propositions. It supplies no proof of either proposition.
The first target compares additive valuations of multiset products under a
pointwise comparison. The second states the root-proximity estimate for a
nonconstant monic polynomial that splits over a discrete valuation ring.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PolynomialRootProximity.lean`.
Its SHA-256 is
`fd5707f0f811be973bcba0f0cc9ad3779344dd958da1af8b8647307cc953775d`.
The [complete pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PolynomialRootProximity.lean>)
was read, including both proofs, to check the signatures and their context.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Source signature | Full adapted target |
| --- | --- | --- | --- |
| M395.001 | private `Polynomial.Splits.addVal_multiset_prod_le` | lines 34–42 | `Langlands.NYLL.PortInternal.M395.d001Statement` |
| M395.002 | `Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivative` | lines 63–70 | `Langlands.NYLL.Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivativeStatement` |

The source context is `noncomputable section` at line 26, `open scoped Polynomial`
at line 28, `universe u` at line 30, and namespace `Polynomial.Splits` at line 32.
There are no additional section variables or local instances.
The source proofs occupy lines 43–54 and 71–145; their terms are omitted.

The internal name follows the published NYLL declaration partition: `M395`
identifies this source module and `d001` its first declaration command. It is a
fresh public target name for a private source helper, not the original private
kernel name. The source helper is used by the second source proof at lines
108–114, which motivates grouping the two related targets.

## Complete propositions and meaning

`Langlands.NYLL.PortInternal.M395.d001Statement.{u, v}` is:

```lean
∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {α : Type v} (s : Multiset α) (f g : α → R)
  (h : ∀ z ∈ s,
    IsDiscreteValuationRing.addVal R (f z) ≤
      IsDiscreteValuationRing.addVal R (g z)),
  IsDiscreteValuationRing.addVal R ((s.map f).prod) ≤
    IsDiscreteValuationRing.addVal R ((s.map g).prod)
```

The ring universe `u` and the multiset-element universe `v` are independent.
The source's `{α : Type*}` is made explicit as `{α : Type v}` without relating
it to `u`. The multiset may be empty, its elements may repeat, and the functions
may take the value zero. The hypothesis is required only for elements of `s`.

`Langlands.NYLL.Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivativeStatement.{u}` is:

```lean
∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (p : R[X]) (hs : p.Splits) (hm : p.Monic)
  (hdeg : p.natDegree ≠ 0) (x : R),
  ∃ y, y ∈ p.roots ∧
    IsDiscreteValuationRing.addVal R (p.eval x) ≤
      IsDiscreteValuationRing.addVal R (x - y) +
        IsDiscreteValuationRing.addVal R (p.derivative.eval y)
```

All source hypotheses are retained: the same three ring instances, splitting,
monicity, nonzero natural degree, and an arbitrary point `x`. The witness `y`
is an element of the canonical root multiset in `R`. Neither separability nor
a nonzero derivative is assumed. `IsDiscreteValuationRing.addVal R` is Mathlib's
`AddValuation R ℕ∞`, with zero valued at `⊤`; the addition and comparison remain
those of `ℕ∞`. Thus repeated roots, zero polynomial values, zero differences,
and zero derivative values remain within the statement's scope.

## Adaptations and reuse

Worker 325 extracted the complete theorem telescopes into `def : Prop` bodies,
preserving their order and explicit, implicit, and instance binder kinds.
The public theorem's name gains the prefix `Langlands.NYLL` and suffix
`Statement`; the private helper uses the internal name explained above.
The polynomial scope is retained. The source's noncomputable section is
unnecessary for proposition definitions and is omitted.

The imports are:

- `Mathlib.Algebra.Polynomial.Splits`
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`

These provide the canonical `Polynomial`, `Polynomial.Splits`,
`Polynomial.Monic`, `Polynomial.natDegree`, `Polynomial.roots`,
`Polynomial.eval`, `Polynomial.derivative`, `Multiset`, `Multiset.map`,
`Multiset.prod`, `IsDiscreteValuationRing`, and
`IsDiscreteValuationRing.addVal`, together with their standard ring,
valuation, and order instances. No alternative polynomial or valuation object
and no new instance is introduced. The source's
`Mathlib.Data.Finset.Max` import supports the maximum-selection step of its
proof and is omitted from these targets. No NYLL module or external repository
is imported.

The published Library and approved Mathlib were searched for both original
names and target names before authoring; no matching declarations were found.
No other worker's draft or compatibility patch is copied. The public partition
records no patch10 edit for this source module.

## Focused checks

Both declarations compiled and were separately inspected in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Each inspection reports
`statement_returns_prop: true`; the reported universe parameters are `u, v`
for the multiset target and `u` for the root-proximity target. These checks
establish that the reduced import list suffices. The unused-variable warnings
for named proof hypotheses reflect their retention as quantified assumptions.
Compilation and inspection do not prove either target.

## Attribution

The original copyright and author header is retained verbatim in the Lean
file, followed by the explicit modification record. The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
