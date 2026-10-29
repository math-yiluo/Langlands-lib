# Reflex-field coefficients of the actual regular Hodge determinant

This module states the coefficient descent needed after the construction
of the complex homogeneous polynomial. It contains a Prop-valued
definition, with no proof of that proposition.

## Source and derived specialization

Robert E. Kottwitz, *Points on Some Shimura Varieties over Finite Fields*,
JAMS 5 (1992), section 5, printed p.389 (PDF p.17), defines the reflex
field as the field of definition of the isomorphism class of the complex
Hodge representation. He then forms the homogeneous determinant of a
linear combination of order-basis elements and states that its
coefficients lie in that field. The source is registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
No source-specific errata note was found in the project notes consulted.

The target here specializes that assertion to the actual left regular
Harris module, with the constructed identity Hodge summand and fixed
conjugated Kottwitz homomorphism. It asks for membership in the
already constructed fixed field of the actual scheme-cocharacter class.
It does not define a new field from the coefficients.
`CocharacterReflexField` identifies this field with the real Hodge
reflex field and the chart reflex field under the same CM-section
hypothesis. Relating the actual regular Hodge representation to that
cocharacter field is part of the proof obligation.

A finite rational-algebra family replaces the source's order basis.
The field-of-definition assertion applies to the determinant of any
such family. This generalization retains the source's order-basis
case without requiring an order for this coefficient-field statement.
Integral coefficient descent is a distinct stronger obligation.

## Exact hypotheses and conclusion

The arithmetic telescope is

```lean
{E K A : Type}
[Field E] [NumberField E] [NumberField.IsTotallyReal E]
[Field K] [NumberField K] [NumberField.IsTotallyComplex K]
[Algebra E K] [Algebra.IsQuadraticExtension E K]
[Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
[Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
{n : ℕ} (D : CentralSimpleUnitaryData E K A n)
{Φ : (E →+* ℝ) → (K →+* ℂ)}
(C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
```

Here `E` is the totally real field in the existing Library notation,
rather than Kottwitz's reflex field. The types `E`, `K` and `A` are
in `Type 0`, matching the current actual scheme-cocharacter
construction. This statement does not enlarge its universe scope.

`KottwitzHodgeDeterminantReflexDescent D C` says that, assuming
`IsCMSection E K Φ`, for every finite index type `ι : Type`, family
`a : ι → A`, and monomial exponent `d : ι →₀ ℕ`, the coefficient

```lean
(D.kottwitzHodgeDeterminant C a).coeff d
```

belongs to `D.kottwitzCocharacterReflexField C` as a subfield of
`ℂ`. The polynomial is the determinant of the constructed Hodge
action, and the field is the fixed field of the Galois subgroup
stabilizing the inner-conjugacy class of the actual first-factor
Kottwitz scheme cocharacter. Neither is an output supplied by the user.
By `mem_complexCocharacterFixedField`, this conclusion is equivalently
fixation of each coefficient by every rational complex automorphism
stabilizing that actual class.

The CM-section condition occurs as a premise of the proposition.
No coefficient membership, semilinear module comparison, representation
descent, or polynomial invariance is assumed.

## Proof and construction obligations

The separate proof must connect the actual Hodge module with the
constructed cocharacter, transport it along rational complex
automorphisms, and obtain determinant invariance from actual
cocharacter conjugacy or an equivalent proved representation
comparison. Calculations for matrix-column weight spaces alone do
not identify the determinant on the whole regular module.

Once this proposition is proved, its coefficient memberships can be
used to construct a polynomial over the indicated field and prove
that its coefficientwise inclusion into `ℂ` is the existing
`kottwitzHodgeDeterminant`. Such a polynomial, its base-change laws,
integrality for order inputs and equality on Lie algebra scheme
sections are subsequent constructions. No descent theorem, PEL
representability or canonical model follows from merely publishing
this statement.

Worker 57 authored this derived target. Independent statement review
does not establish the truth of the proposition.
