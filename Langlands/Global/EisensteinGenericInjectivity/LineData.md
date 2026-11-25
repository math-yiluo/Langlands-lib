# A Chevalley line adapted to the split component of a parabolic

Module `Langlands.Global.EisensteinGenericInjectivity.LineData` proves `exists_lineData`: for a
parabolic `p : P → G` of a connected reductive group over a field, with a parabolic root
presentation `r : ParabolicRootPresentation p l a` whose split component `A` is a split torus,
there is a matrix representation of `G` with a coordinate line whose stabilizer is `P`, which
diagonalizes the cocharacter of the split component, and whose orbit matrices have strictly
smaller weights off that line. The frequency separation of the module
`Langlands.Global.EisensteinGenericInjectivity.Separation` starts from these data.

The declaration is in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`. Its complete type is printed by `PrettyPrinter.ppSignature` (the `#check` form), with the
namespaces of the page of `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declaration

- `exists_lineData r hA hG`: there are `N`, a coordinate index `j : Fin N`, a matrix
  representation `σ : G → GL_N` and integer weights `e : Fin N → ℤ` such that
  1. `p : P → G` is exactly the stabilizer of the coordinate line `j`
     (`σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j`, on all test schemes);
  2. along the split-component cocharacter `ζ = r.splitComponentCocharacter`, the cocharacter
     `ζ ≫ a ≫ l ≫ p ≫ σ` is the diagonal cocharacter with weights `e`;
  3. every entry `(i, j)` with `i ≠ j` and `e j ≤ e i` of every point matrix of `σ` vanishes
     (`σ.HasStrictOrbitWeightUpperBound e j`).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exists_lineData.{u} {F : Type u} [Field F]
    {G P M : Langlands.GroupScheme (Spec ↧F)} {A : Langlands.CommGroupScheme (Spec ↧F)}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) (hA : IsSplitTorus A.toGrp) (hG : G.IsConnectedReductive) :
    ∃ N j σ e,
      σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j ∧
        (Langlands.CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) ≫ σ =
            GeneralLinear.diagonalCocharacter (Fin N) (↧F) e ∧
          σ.HasStrictOrbitWeightUpperBound e j
  ```

## Proof

- Chevalley's theorem in the form of the Library theorem `Chevalley.exists_line_stabilizer`
  (module `Langlands.GroupScheme.Chevalley.ActualLineStabilizer`) gives a representation with a
  coordinate line whose exact stabilizer is `P`.
- The split torus `A`, mapped to `G` by `a ≫ l ≫ p`, preserves the line. The Library
  construction `torusEigenlineDiagonalization` (module
  `Langlands.GroupScheme.MatrixRepresentation.TorusEigenlineDiagonalization`) changes the basis so
  that `A` acts diagonally while the line stays a coordinate line;
  `HasExactCoordinateLineStabilizer.basisConjugate` transports the stabilizer property, and the
  diagonal characters paired with `ζ` give the weights `e`.
- The Library theorem `ParabolicRootPresentation.parabolic_eq_splitComponentCocharacter` (module
  `Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter`) identifies `P` with the
  parabolic of the cocharacter `ζ ≫ a ≫ l ≫ p`, and
  `hasStrictOrbitWeightUpperBound_of_parabolic_eigenline` (module
  `Langlands.GroupScheme.MatrixRepresentation.ParabolicOrbitWeightGap`) turns the eigenline of a
  dynamic parabolic into the strict weight gap.

## Sources

The statement assembles Library results; their pages give the literature. No further source.
