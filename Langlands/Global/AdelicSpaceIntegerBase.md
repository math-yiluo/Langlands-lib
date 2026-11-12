# Integer bases for cofinal actual adelic models

Author: Worker 109.

This internal adapter derives local finite type of the actual integer-base
maps needed for arithmetic space-model composition. It uses the published
`NumberFieldPrincipalSIntegerFiniteType` and
`CurvePlacePrincipalSIntegerFiniteType` constructions and Mathlib's affine
finite-type comparison. No external literature theorem is claimed as proved
here. All global fields and coefficient rings retain arbitrary universe `u`.

`AdelicSpaceIntegerBase.algebra C` provides the canonical algebra structure
of any commutative ring `C : Type u` over `ULift.{u} ℤ`. It is the existing
`ULift.algebra'` construction applied to the usual integer action. It is
instance-reducible but not registered as a global instance, so callers can
install the chosen structure locally.

`locallyOfFiniteType C` assumes `Algebra.FiniteType ℤ C` and allows any
algebra structure of `C` over the lifted integers. There is a scalar tower
`ℤ → ULift ℤ → C` because the two ring homomorphisms from the original
integers to `C` agree by their uniqueness. Finite type over the original
integers therefore gives finite type over the lifted integers by
`Algebra.FiniteType.of_restrictScalars_finiteType`. The actual affine
scheme/ring-hom comparison `HasRingHomProperty.Spec_iff` then proves local
finite type of `Spec.algebraMap (ULift ℤ) C`.

`numberField_cofinal K S` applies this result to the literal outside-set
integer ring of the published `numberFieldPrincipalLevelAbove K S`.
That construction returns an actual finite-place level containing `S` and
proves its actual ring finite type over `ℤ`.
`curvePlace_cofinal k F S` applies the same argument to the literal ring
`curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val`.
The given global function-field presentation and finite constant field are
exactly the hypotheses of its published finite-type result. Both conclusions
install the canonical lifted-integer algebra locally and prove local finite
type of that actual base map.

The module thus discharges the arithmetic integer-base local-finite-type
premise at actual cofinal principal levels, for arbitrary initial finite
sets in both characteristics. It does not assert finite type for every
arbitrary outside-set ring. It does not spread algebraic-space morphisms or
prove a uniform finite-field estimate or the unconditional adelic target.
