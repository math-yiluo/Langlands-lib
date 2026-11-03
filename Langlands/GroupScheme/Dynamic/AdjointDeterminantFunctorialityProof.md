# Proof of functoriality of the actual adjoint determinant

`dynamicAdjointDeterminantFunctoriality` proves the published target
`DynamicAdjointDeterminantFunctorialityStatement.{u}` at an arbitrary universe
`u`. Its type is exactly that proposition. The hypotheses are unchanged: every
commutative base ring, the actual represented dynamic `P` and `U` of a
cocharacter, affine `U → Spec R` and affine `P`, and natural finite coordinates
`c` on the actual Lie kernel of `U`. Here `a` is `parabolicAdjointAction hP hU`
and `δ` is `adjointDeterminantCharacter hP hU c`. The proof adds no premise. It
covers every algebra homomorphism, nonreduced test algebras, arbitrary
characteristic and rank `d = 0`.

## The four conjuncts

1. **Differential naturality.** For `f : A ⟶ B` this is the published
   `AutomorphicAction.differential_naturality` applied to `f.hom`. The point map
   `P.affinePointMap f` is by definition `Lie.affineMap P f.hom`, so the
   published statement has exactly the required form.
2. **Determinant naturality.** This is the published
   `AutomorphicAction.differential_det_naturality c f p`. The canonical group and
   module structures named by the target's `letI` bindings are the global
   instances `lieKernelCommGroup` and `lieKernelModule`. The published lemma
   uses these same instances, so no comparison of instances is needed.
3. **Character-value naturality.** `adjointDeterminantCharacter_affinePoints`
   identifies the `Gm`-coordinate of `δ` at a point with the intrinsic
   determinant of the differential at that point. The proof applies it at
   `P.affinePointMap f p` over `B`, then uses determinant naturality, then
   applies the same identification over `A` inside `Units.map f`.
4. **Restriction of the acting group.** For an affine `H` and `j : H ⟶ P`, the
   equality of differentials is the published
   `AutomorphicAction.differential_restrict j h`. The character equality
   `characterRestrict j δ = (a.restrict j).determinantCharacter c` is
   `AutomorphicAction.determinantCharacter_restrict`, proved below.

## Helper results

These helper results are new. Each one is proved in this module.

- `MatrixRepresentation.ext_affineMatrix`: over an affine group scheme `H`, two
  matrix representations `H ⟶ GL_n` are equal if their matrices agree at every
  affine test point. The proof evaluates both at the scheme map
  `e.hom.hom.hom` of the coordinate isomorphism
  `e = AffineCoordinates.groupSchemeIso H`. This map is an affine point of `H`,
  over the chosen coordinate algebra. `GeneralLinear.affinePointsEquiv` is
  injective, so the two composites with `e.hom.hom.hom` are equal. Composing with
  `e.inv.hom.hom` cancels that map, because `e.inv ≫ e.hom = 𝟙`. This gives
  equality of the underlying scheme maps, and `Grp.hom_ext` finishes the proof.
- `AutomorphicAction.coordinateAction_restrict` and
  `AutomorphicAction.coordinateMatrix_restrict`: the coordinate differential and
  the coordinate matrices of `a.restrict j` at `h` equal those of `a` at
  `h ≫ j.hom.hom`. Both follow from `differential_restrict`, using the same
  coordinates `c` on the same `U`.
- `AutomorphicAction.finiteRepresentation_restrict`:
  `(a.restrict j).finiteRepresentation c = j ≫ a.finiteRepresentation c`. By
  `ext_affineMatrix` it suffices to compare affine matrices. By
  `finiteRepresentation_affineMatrix` the left side has the coordinate matrix of
  the restricted action. The right side has the matrix of
  `a.finiteRepresentation c` at `h ≫ j.hom.hom`, which is again a coordinate
  matrix. The two agree by `coordinateMatrix_restrict`.
- `AutomorphicAction.determinantCharacter_restrict`: both characters are defined
  through `characterRestrict` into the general-linear determinant character.
  `finiteRepresentation_restrict` rewrites the right-hand side, and
  `characterRestrict_comp` turns restriction along a composite into iterated
  restriction.

## Scope

The theorem compares constructions under the target's conditional inputs. It
proves functoriality for coefficient maps and for restriction of the acting
group on the same `U` with the same finite coordinates. It makes no claim about
ambient homomorphisms that change `U`. No Haar measure, absolute value, square
root or analytic modulus identity is involved. The proof axioms are `propext`,
`Classical.choice` and `Quot.sound`.
