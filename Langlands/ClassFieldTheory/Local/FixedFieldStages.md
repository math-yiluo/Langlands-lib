# Fixed-field finite stages of algebraic-closure units

This internal construction works for every characteristic-zero field
`K : Type u`, with arbitrary common universe `u`. It connects the existing
absolute unit module, fixed-unit quotient representations, and relative
cohomology without changing their definitions. All declarations are in
`Langlands.ClassFieldTheory.Local`.

`absoluteUnitDiscreteModule K` bundles `absoluteUnits K` as a discrete
module over `IntegerScalars.{u}` for `Field.absoluteGaloisGroup K`.
Its jointly continuous action is certified by the published
`continuous_unitAction K (AlgebraicClosure K)`. This bundle itself does
not require characteristic zero.

For an open normal subgroup `N`, `finiteStageFixedField K N` is exactly
`IntermediateField.fixedField N.toSubgroup`. The auxiliary
`finiteStageClosedSubgroup` uses the same subgroup and the fact that an
open subgroup is closed. The infinite Galois correspondence identifies
its fixing subgroup with `N`; openness then proves finite dimensionality.
Normality proves that the fixed field is Galois over `K`.
`finiteStageRelativeIso K N q` specializes the published
`fixedFieldCohomologyIso` to this closed subgroup. Its source is
`groupCohomology (finiteQuotientRep (absoluteUnitDiscreteModule K).toRep N) q`,
and its target is `relativeCohomology K (finiteStageFixedField K N) q`,
for every natural degree `q`.

For a finite Galois intermediate field `E` of `AlgebraicClosure K`,
`finiteGaloisFixingSubgroup K E` bundles the actual subgroup
`E.fixingSubgroup`, with Mathlib's openness and normality certificates.
`finiteGaloisFixingSubgroup_toSubgroup` states the underlying subgroup
equality, and `finiteStageFixedField_finiteGaloisFixingSubgroup` states
that the resulting fixed field is `E`.

The direct identification with the specified field `E` uses explicit
maps, avoiding transport of the entire cohomology object through that
field equality:

- `finiteGaloisStageGroupEquiv K E` descends
  `AlgEquiv.restrictNormalHom E` to the quotient by `E.fixingSubgroup`.
  Surjectivity of restriction and the calculation of its kernel prove
  that this is an equivalence. `finiteGaloisStageGroupEquiv_mk` identifies
  its value on the class of `σ` with `closureRestriction K E σ`;
  `finiteGaloisStageGroupEquiv_symm_restriction` gives the inverse formula.
- `finiteGaloisStageUnitsAddEquiv K E` takes an invariant closure unit
  to the unit of `E` with the same underlying value. Membership follows
  from the published fixed-unit equivalence and the infinite Galois
  correspondence. Its inverse is the actual inclusion of `E` units
  into closure units, whose invariance follows from the definition of
  the fixing subgroup. Unit and subtype extensionality prove the
  inverse identities and additivity.
- `finiteGaloisStageUnitsLinearEquiv K E` supplies linearity over the
  unchanged lifted integer scalars by preservation of integer multiples.
  Its `_val` and `_symm_val` lemmas express equality of underlying values
  and identify its inverse with `unitInclusionLinear E (AlgebraicClosure K)`.
  Its `_inclusion` lemma states that inclusion after the forward map is
  the original invariant unit.
- `finiteGaloisStageUnitsLinearEquiv_intertwines` proves equivariance
  for the actual quotient action and restriction group equivalence.
  Quotient induction reduces it to an automorphism of the closure;
  linear-map, unit, and subtype extensionality then reduce it to
  `AlgEquiv.restrictNormal_commutes`.

`finiteGaloisStageRelativeIso K E q` is the existing
`groupCohomology.mapIso` applied to these two explicit equivalences and
their proved equivariance. Its target is directly
`relativeCohomology K E q`, and its source is the fixed-unit quotient
cohomology for `finiteGaloisFixingSubgroup K E`.

The precise interfaces and certificates are internal bridges to the
published `FixedFieldUnits`, `ClosureCoefficients`, and Mathlib infinite
Galois correspondence APIs. Their mathematical context is Serre,
*Local Fields* (1979), Chapter X, §§3–4, printed pages 154–156
(PDF pages 160–162), registered as `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These pages explain infinite Galois cohomology and its passage through
finite Galois subextensions; they do not specify these Lean interfaces.
This module constructs the stage identifications only. Compatibility
squares, vanishing, exactness, and comparison with continuous cohomology
are separate results.
