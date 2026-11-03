# Exact all-test formula for the actual adjoint determinant: proof

This module proves `Langlands.GroupScheme.DynamicAdjointDeterminantFormulaStatement`
from `Langlands.GroupScheme.Dynamic.AdjointDeterminantFormulaStatement`. The theorem
`Langlands.GroupScheme.dynamicAdjointDeterminantFormula` has exactly that type, at an
arbitrary universe `u`.

The proof introduces the base ring `R`, the group schemes `G`, `P`, `U`, the
cocharacter `χ`, the inclusions `iP`, `iU`, the representation witnesses `hP`, `hU`,
the two affineness instances, the rank `d` and the natural finite coordinates `c`.
The three `let`-bound terms of the statement are the constructions themselves:
`a` is `Dynamic.parabolicAdjointAction hP hU`, `ρ` is `a.finiteRepresentation c`, and
`δ` is `Dynamic.adjointDeterminantCharacter hP hU c`. Each of the four conjuncts is
then closed by an existing published comparison applied to these terms:

- Scheme-test conjugation: `Dynamic.parabolicAdjointAction_act_comp hP hU p u` gives
  `a.act p u ≫ iU.hom.hom = (p ≫ iP.hom.hom) * (u ≫ iU.hom.hom) * (p ≫ iP.hom.hom)⁻¹`
  for every `T : Over (Spec R)`, `p : T ⟶ P.X` and `u : T ⟶ U.X`. This is the positive
  orientation `p*u*p⁻¹`.
- Affine-test differential: `AutomorphicAction.finiteRepresentation_affineAction`
  for the action `a` gives `ρ.affineAction A p (c.equiv A x) = c.equiv A (a.differential p x)`
  for every commutative `R`-algebra `A`, `p : P.affinePoints A` and
  `x : Additive (lieKernel U A)`.
- Affine-test intrinsic determinant: `Dynamic.adjointDeterminantCharacter_affinePoints`
  gives the identity of `Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom (p ≫ δ.toMul.hom.hom)`
  with `LinearEquiv.det (a.differential p)`, a unit of the coefficient algebra `A`. The
  statement's two `letI` instances, `lieKernelCommGroup U` and `lieKernelModule U`, are the
  canonical instances already used by `differential` and `Lie.FiniteCoordinates`, so the
  published lemma closes the goal as stated.
- Scheme-test character evaluation: `AutomorphicAction.determinantCharacter_eval` for the
  action `a` gives `characterEval δ T p = Matrix.GeneralLinearGroup.det (ρ.pointMatrix T p)`
  for every `T : Over (Spec R)` and `p : T ⟶ P.X`, with values in units of the global
  sections of `T`. This uses that `Dynamic.adjointDeterminantCharacter hP hU c` is by
  definition `a.determinantCharacter c`.

No hypothesis is added beyond those of the statement. The base ring has arbitrary
characteristic, affine tests include nonreduced algebras, scheme tests are arbitrary
objects over `Spec R`, and `d` may be zero. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The determinant here is the algebraic one, with positive conjugation orientation. The
motivating local-field conventions of Renard (§V.3.1–V.3.4, §V.5.4) and Waldspurger
(2003, §I.1) are recorded in the statement's Markdown. Haar measures, absolute values,
square roots and analytic modulus identities are not part of this result.
