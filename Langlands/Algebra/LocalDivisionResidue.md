# Compact integers and finite residue of a local division algebra

Let `K` be a field with a valuative relation and a compatible topology making
it a nonarchimedean local field. Let `D` be a finite-dimensional central division
`K`-algebra. Both carriers belong to the same arbitrary universe `u`.
There is no characteristic restriction and no norm or topology on `D` is assumed.
Write `v = localReducedNormValuation K D`, the valuation obtained by applying
the original valuation of `K` to the canonical reduced norm.

In namespace `Langlands.CentralDivision`, this module constructs
`localDivisionNormedRing K D` and `localDivisionNormedAlgebra K D`.
They specialize the normalized determinant norm to the complete ultrametric
norm `LocalGalois.localNormedField K` constructed from the given local-field
valuation. The norm is

```
‖x‖ = ‖Algebra.norm K x‖ ^ (Module.finrank K D : ℝ)⁻¹.
```

The ring operations and scalar action are the original ones. The normed
structures are explicit instance-reducible definitions. All norm and compactness
statements in this module use the constructed normed-ring structure explicitly.

The comparison theorems state, for every `x : D`,

```
‖x‖ ≤ 1 ↔ v x ≤ 1,
‖x‖ < 1 ↔ v x < 1.
```

Consequently, `localDivisionInteger_eq_closedBall` identifies the actual integer
set `(v.integer : Set D)` with `Metric.closedBall (0 : D) 1`, and
`localDivisionInteger_isCompact` proves that this set is compact.
The compactness is in the constructed compatible finite-dimensional norm topology.

The instance `localDivisionResidue_finite` proves

```
Finite (DivisionValuation.Residue v).
```

Here `DivisionValuation.Residue v` is the actual quotient of `v.integer` by
the two-sided ideal of elements of value strictly less than one, with the
division-ring operations constructed in `DivisionValuationResidue`.
`localDivisionResidueField K D` applies Mathlib's little Wedderburn theorem to
give a field structure extending those operations.
`localDivisionResidue_mul_comm` explicitly proves commutativity for the
multiplication already present on this quotient.

## Implemented proofs and internal provenance

These constructions and proofs are internal consequences of the imported
normalized regular norm, local reduced-norm valuation and actual residue
quotient, together with Mathlib's finite-dimensional topology, compact-cover
and finite-division-ring theorems. No external structural premise is added.

The positive dimension root preserves strict and non-strict comparisons of
regular determinant absolute values. The base-field norm comparison
`LocalGalois.localNormedField_le` converts these to comparisons for the original
base valuation. The regular-norm formula is

```
valuation K (Algebra.norm K x) = v x ^ CentralSimple.reducedDegree K D.
```

Since the reduced degree is positive, an ordered nonnegative value has its
reduced-degree power at most one, or strictly less than one, exactly when the
value itself does. This proves both unit-ball comparisons. For the strict
base comparison, negate the reversed non-strict comparison.

The constructed scalar norm is the given local-field norm. The topology of
that field norm is the originally supplied topology, which is locally compact.
Thus Mathlib's `FiniteDimensional.proper K D` makes `D` proper in the constructed
norm, and its closed unit ball is compact.

Cover this compact integer set by finitely many open balls of radius one with
centers in the same integer set. Map each center, regarded as an original
integral element, to its actual reduction. Every residue class has an integral
representative, and that representative lies within distance strictly less than
one of a center. The difference therefore has norm less than one, hence
valuation less than one. `DivisionValuation.reduction_eq_iff` makes the two
reductions equal. Reduction of the finite set of centers is consequently
surjective onto the actual residue quotient, proving finiteness.

Finally, Mathlib's `littleWedderburn` extends the existing division-ring
structure of a finite division ring to a field. Its multiplication is the
original quotient multiplication, so its commutativity also proves the last
explicit equality theorem.

## Scope

This module proves compactness of the actual local integer set and finiteness
and commutativity of the actual residue division ring in arbitrary characteristic.
It does not assert that the unscaled reduced-norm valuation is surjective onto
its stated value group. It does not identify the residue-field extension of the
base residue field, compute its degree, construct unramified or cyclic maximal
subfields, or prove local SK1 or the local Kneser–Tits theorem.
