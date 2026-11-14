# Smooth integral models of maximal algebraically bounded subgroups

`Langlands.GroupScheme.maximalBoundedIntegralModel` proves exactly
`Langlands.GroupScheme.MaximalBoundedIntegralModelStatement.{u}` at arbitrary
universe `u`. The statement is imported unchanged from
`Langlands.GroupScheme.IntegralModel.MaximalBounded`.

Let `K` be a valued field whose canonical valuation integer ring `R` is a
Henselian discrete valuation ring with algebraically closed residue field.
For a smooth affine group scheme `G` over `Spec K` and a subgroup `B` maximal
among algebraically bounded subgroups of the actual `rationalPoints G`, the
theorem constructs an actual `L : IntegralModel R K G` with `L.IsSmooth`
and the literal subgroup equality `L.integralPoints = B`. Algebraic boundedness
is the published predicate on all global regular functions of `G`.

## Provenance

This is the maximal-subgroup paragraph in the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 8.3.1, printed
pp. 295–296 / PDF pp. 326–327, especially printed p. 296 / PDF p. 327.
The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
It is a derived subresult of the source's vertex argument: once the maximal
bounded subgroup is supplied, this paragraph needs no connectedness,
reductivity, building or openness hypothesis.

The registered 2024 corrections, source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 37 adds perfectness of the residue field to Section 8.3. The
algebraically closed residue field here is perfect.

## Implemented proof

The proof imports and applies the published existence theorems
`boundedSubgroupStableLattice`, `generalLinearLatticeIntegralModel`,
`integralModelSchematicClosure` and `IntegralModel.smoothening_exists`.
All four construction inputs are discharged; the theorem has no additional
premise.

First, `affineLinearEmbeddingStatement` supplies a closed finite-dimensional
representation `ρ` of the original group. The theorem
`boundedSubgroupStableLattice`, from
`Langlands.GroupScheme.BoundedSubgroupStableLatticeProof`, supplies an actual
full lattice `Λ` preserved by `B`. Its construction is the `R`-span of the
translates of the standard coordinate basis.

The theorem `generalLinearLatticeIntegralModel`, from
`Langlands.GroupScheme.IntegralModel.GeneralLinearLatticeProof`, supplies a
smooth ambient model `M` of the general linear group whose integral points
are exactly the lattice stabilizer. It chooses an integral basis of `Λ`
and uses the standard general linear group over `R`. Its generic
identification is the standard base-change identification followed by
conjugation by that basis matrix. Thus its literal integral points are the
matrices preserving `Λ` in both directions.

Let `D` be the inverse image of `M.integralPoints` under the rational-point
map of `ρ`. The subgroup property of `B` supplies stability under inverse
matrices, so `B ≤ D`. In Lean, the two rational-matrix identifications agree
by extensionality of units, and `Matrix.coe_units_inv` relates the inverse
unit to the nonsingular matrix inverse. The published theorem
`MatrixRepresentation.isAlgebraicallyBounded_of_preserves_lattice` proves
that `D` is algebraically bounded. Maximality gives `B = D`.

The theorem `integralModelSchematicClosure`, from
`Langlands.GroupScheme.IntegralModel.SchematicClosureProof`, constructs the
schematic closure `C` of the original generic group in the ambient model.
Its scheme is the scheme-theoretic image of the generic map to `M`, with
group operations restricted from `M`. The map from `G` to the generic fibre
of `C` is an isomorphism; its inverse is `C.genericIso`. The resulting
model morphism is compatible with `ρ`. The published equality
`Hom.IsSchematicClosure.integralPoints_eq_comap` gives
`C.integralPoints = D` through this specified generic identification.

Finally, `IntegralModel.smoothening_exists`, from
`Langlands.GroupScheme.IntegralModel.SmootheningProof`, supplies an actual
smooth model `L` and a morphism `π : L.Hom C (𝟙 G)` that is a smoothening.
The imported construction uses the spectrum of the Hopf algebra of generic
regular functions on `C` that are integral on its `R`-sections. Its generic
identification is the base change of `π.hom` followed by `C.genericIso`.
The smoothening theorem proves finite type, flatness, smoothness and
bijection on actual `R`-sections. Since `π` is compatible with the identity
of `G`, `IsSmoothening.integralPoints_eq` gives the literal equality
`L.integralPoints = C.integralPoints`. Composing with `C.integralPoints = D`
and `D = B` yields the required equality in the original rational-point
group.

This proves the model construction for a supplied maximal bounded subgroup.
Existence of such a subgroup and the other integral-model axioms are separate
statements.
