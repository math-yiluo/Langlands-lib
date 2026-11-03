# Proof: existence of the actual adjoint determinant on P and M

This module proves the published statement
[`DynamicAdjointDeterminantExistenceStatement`](AdjointDeterminantExistenceStatement.md):

```lean
theorem Langlands.GroupScheme.dynamicAdjointDeterminantExistence :
    DynamicAdjointDeterminantExistenceStatement.{u}
```

Let `k` be a field, `G` a connected reductive group over `Spec k` and `χ` a
cocharacter. Let `iP : P ⟶ G`, `iM : M ⟶ G` and `iU : U ⟶ G` represent the
dynamic parabolic, centralizer and unipotent subgroups of `χ`. The proof
supplies the affineness of `P`, `M` and `U`, the canonical finite
coordinates of `Lie(U)`, the representation constructed from
`parabolicAdjointAction`, and the characters `adjointDeterminantCharacter` on
`P` and the determinant of `centralizerAdjointAction` on `M`. It then checks
the Levi restriction identity and the three point formulas.

The route is internal to the Library. It does not use the unproved structural
targets `DynamicAdjointDeterminantStructureStatement` or
`DynamicAdjointDeterminantFormulaStatement`.

## Auxiliary lemma

`AutomorphicAction.characterRestrict_determinantCharacter`. Let
`a : AutomorphicAction H U` be an action with `U` affine over `Spec R` and `H`,
`K` affine schemes. Let `c` be finite coordinates on `Lie(U)` and
`j : K ⟶ H` a homomorphism. Then

```
characterRestrict j (a.determinantCharacter c) = (a.restrict j).determinantCharacter c.
```

Characters are determined by their values on all points
(`rationalCharacters.ext_characterEval`). Since `K.X` is affine, it is
isomorphic over `Spec R` to `Spec B` for an `R`-algebra `B`
(Mathlib's `essImage_algSpec`). So every point `x` factors as
`(x ≫ e.inv) ≫ e.hom`, and `characterEval_naturality` reduces both sides to
the affine point `e.hom`. On affine points, `determinantCharacter_eval_affine`
computes both sides as the determinant of a differential. These differentials
agree by `differential_restrict`:
`(a.restrict j).differential m = a.differential (m ≫ j)`.

## Main proof

1. **Affineness of `G`.** `IsConnectedReductive` gives `G.X.hom` affine and
   smooth, so `G.X.left` is affine (`isAffine_of_isAffineHom`).
2. **Closed inclusions.** `Dynamic.Affine` supplies closed subgroup
   representatives `parabolicHom χ`, `centralizerHom χ` and `unipotentHom χ`
   (`isRepresentedBy_*Hom`, `isClosedSubgroup_*Hom`). Two representatives of
   the same subgroup functor are isomorphic compatibly with the inclusions
   (`isoOfIsRepresentedBy_hom_comp`). So each given inclusion is an
   isomorphism followed by a closed immersion, and `IsClosedSubgroup.iso_comp`
   shows that `iP`, `iM` and `iU` are closed subgroups.
3. **Affineness of `P`, `M`, `U`.** `IsClosedSubgroup.isAffineHom` gives the
   three `IsAffineHom` witnesses that the statement asks for. `P` and `M` are
   then affine schemes.
4. **Finite type of `U`.** `U.X.hom = iU ≫ G.X.hom` (`Over.w`). A closed
   immersion is locally of finite type, and so is the smooth morphism
   `G.X.hom`.
5. **Coordinates.** With `U` affine and locally of finite type over the field,
   `c := Lie.finiteCoordinates U` gives natural coordinates of rank
   `d = finrank_k Lie(U)(k)`.
6. **Witnesses.** `ρ := (parabolicAdjointAction hP hU).finiteRepresentation c`,
   `δP := adjointDeterminantCharacter hP hU c` and
   `δM := (centralizerAdjointAction hM hU).determinantCharacter c`. The first,
   second and fourth equations hold by `rfl`.
7. **Levi restriction.** Restricting `parabolicAdjointAction hP hU` along
   `centralizerToParabolic hP hM` gives `centralizerAdjointAction hM hU`.
   This is `eq_centralizerAdjointAction`. After the inclusion of `U`, the
   restricted action is `restrict_act` followed by
   `parabolicAdjointAction_act_comp`. Then `centralizerToParabolic_comp`
   (`centralizerToParabolic hP hM ≫ iP = iM`) turns it into
   `m*u*m⁻¹` computed in `G`. The equation
   `δM = characterRestrict (centralizerToParabolic hP hM) δP` follows from the
   auxiliary lemma.
8. **Point formulas.** The action formula is
   `finiteRepresentation_affineAction`. The determinant formulas on `P` and `M`
   are `adjointDeterminantCharacter_affinePoints` and
   `determinantCharacter_affinePoints`. All hold on every test algebra.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
