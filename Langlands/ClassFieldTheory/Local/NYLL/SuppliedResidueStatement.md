# Supplied residue equality and the discrete valuation

Worker 449 authored the Lean and Markdown for this internal, derived
statement interface; Worker 109 specified the supplied-data comparison.
The module defines one proposition,
`Langlands.LocalClassField.NYLL.SuppliedResidueCongruenceStatement.{u}`,
with complete unapplied type `Prop`. It supplies no proof of that proposition.

For every `p : ℕ` with `[Fact p.Prime]`, every
`F : Langlands.PadicField.{u} p`, every `T : F.TopologicalData`, and every
`x y : T.Integers`, the target is exactly

```text
T.residue x = T.residue y ↔
  T.discreteValuation ((x : F.Carrier) - (y : F.Carrier)) < 1.
```

The carrier universe `u` is arbitrary. There is no additional hypothesis
identifying the residue quotient with the valuation, and no restriction to
canonical topological data.

## Existing objects and semantics

The only import is
[`Langlands.LocalField.Normalization.Definitions`](../../../LocalField/Normalization/Definitions.md).
After locally installing `T.valuativeRel`, write
`v = ValuativeRel.valuation F.Carrier`. The existing `T.Integers` is
exactly `v.integer`, the subring defined by `v a ≤ 1`.
`T.ResidueField` is exactly `IsLocalRing.ResidueField T.Integers`,
the quotient by the maximal ideal of this actual integer ring.
`T.residue` is exactly `IsLocalRing.residue T.Integers`, its quotient
ring homomorphism. These are the imported definitions themselves, rather
than replacement presentations requiring a comparison isomorphism.
In the same module, `T.residueCardinality` is defined as
`Nat.card T.ResidueField`.

The imported `T.discreteValuation` locally installs `T.topology`,
`T.valuativeRel`, and `T.localField`. It composes `v` with the ordered
multiplicative isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier`
to `WithZero (Multiplicative ℤ)`. Thus the inequality in the target uses
the actual supplied discrete valuation.

The inspected Mathlib interfaces explain the semantics of this target.
`IsLocalRing.residue_eq_zero_iff` identifies residue zero with membership
in the maximal ideal. `Valuation.Integer.not_isUnit_iff_valuation_lt_one`
identifies a nonunit of a valuation integer ring with valuation strictly
below one; `Valuation.mem_maximalIdeal_iff` gives the corresponding
maximal-ideal membership criterion for the valuation subring.
Applying these interfaces to the difference of two integers, and
transporting the strict inequality through the ordered value-group
isomorphism, is the intended later proof route. This paragraph describes
the obligation; the Lean file does not implement its proof.

## Intended use

For integral `z x : T.Integers` and `q : ℕ`, a later proof can apply the
target to `z` and `x ^ q`. Together with `map_pow` for `T.residue` and
the subtype coercion law for powers, this converts

```text
T.residue z = (T.residue x) ^ q
```

to

```text
T.discreteValuation ((z : F.Carrier) - (x : F.Carrier) ^ q) < 1.
```

The specialization `q = 1` also supplies the congruence criterion needed
for an inertia clause. If an integral field element is supplied by a
hypothesis `T.discreteValuation a ≤ 1`, later consumers should reuse
`Langlands.PadicField.TopologicalData.mem_integers_iff_discreteValuation_le_one`
from `Langlands.HarmonicAnalysis.Conductor` to obtain its membership
proof and hence its element of `T.Integers`. This module neither duplicates
that theorem nor introduces a new integer-ring construction.

The analogous
`Langlands.ClassFieldTheory.Local.UnramifiedBaseChange.residue_eq_iff`
in `Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeProof`
concerns `LocalGalois.extensionIntegers` and a spectral-norm inequality.
It is not the supplied-data discrete-valuation target defined here.

## Provenance and boundary

The proposition is an internal comparison target derived from the existing
Library constructions and the inspected Mathlib quotient and valuation
interfaces. It copies no external source or NYLL implementation and is
independent of a reciprocity map or a NYLL port. No new construction,
global instance, axiom, or proof of the target is introduced.
In particular, this statement does not establish any Artin action or its
normalization. Its later proof and applications are separate work.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation and complete-declaration inspection check this statement's
elaboration and universe scope; independent semantic acceptance and
Integrator publication remain required before a proof child can use it.
