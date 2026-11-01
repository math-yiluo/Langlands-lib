# The `H¹` dimension bound for abelian schemes over a field, from Künneth and vanishing

Author: Worker 274.

This module proves `Langlands.AbelianScheme.fieldStructureSheafH1DimensionBound_of`: the
published proposition `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`
follows from two hypotheses,

1. `Langlands.Cohomology.Cech.KunnethDetectionStatement` (module
   `Langlands.AlgebraicGeometry.CechKunnethStatement`), and
2. for every field `k`, abelian scheme `A` over `Spec k` and `g` with
   `A.HasRelativeDimension g`, the module
   `(relativeCohomology A.X.hom (g + 1)).obj (structureSheaf A.X.left)` is zero.

It also proves `Langlands.AbelianScheme.vanishing_of`: hypothesis 2 follows from the published
statements `Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement` (a quasi-compact
smooth scheme of relative dimension `g` over a field has topological Krull dimension at most
`g`) and `Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`
(quasi-coherent cohomology of a noetherian separated scheme of dimension at most `d` vanishes in
degrees `n > d`). Hence `fieldStructureSheafH1DimensionBound_of_statements` proves the published
proposition from these two statements and the Künneth detection statement. Finally,
`fieldStructureSheafH1DimensionBound_of_dim_of_vanishing` discharges the Künneth detection
statement with `Langlands.Cohomology.Cech.kunnethDetection` (module
`Langlands.AlgebraicGeometry.CechKunneth`, by Worker 921), so the published proposition follows
from the two published statements alone.

It contains no `sorry` and no new axioms. It is an intermediate step of the proof; the final
proof module discharges the remaining hypotheses with their published proofs.

## Proof

Fix `k`, `A` and `g`, and the standard derived categories. Write `X = A.X.left` and
`πX = A.X.hom`.

- The fibre product is `pullback πX πX = (A.X ⊗ A.X).left` with projections `pullback.fst`
  and `pullback.snd` (the cartesian monoidal structure of `Over S` is given by pullbacks).
  The multiplication is `m = μ[A.X].left`, the unit point is `e = η[A.X].left` with
  `e ≫ πX = 𝟙` (`Over.w`), and the axes are `i₁ = (lift (𝟙 A.X) (toUnit A.X ≫ η)).left` and
  `i₂ = (lift (toUnit A.X ≫ η) (𝟙 A.X)).left`. Their projections follow from `lift_fst` and
  `lift_snd`, and `i₁ ≫ m = 𝟙`, `i₂ ≫ m = 𝟙` from the unit laws
  `MonObj.lift_comp_one_right` and `MonObj.lift_comp_one_left`.
- Global functions are constant: `surjective_secHom_top`, since `A` is smooth, proper and
  geometrically connected.
- `exists_affineCover` gives a finite cover `U` by affine opens; since `πX` is separated over the
  affine base, intersections of affine opens are affine (`isAffineHom_diagonal_iff`), so all
  finite intersections are affine (`Cech.isAffineOpen_inter`).
- The structure sheaf is quasi-coherent, hence Čech-acyclic; with hypothesis 2,
  `CechShift.exactAt_of_isZero` gives `Cech.ExactAt` in degree `g + 1` for `U`.
- `Cech.finiteDimensional_and_finrank_le` with hypothesis 1 gives the conclusion; the module
  `structureSheaf A.X.left` is by definition `SheafOfModules.unit A.X.left.ringCatSheaf`.

For `vanishing_of`: `A.X.left` is quasi-compact (`QuasiCompact.compactSpace_of_compactSpace`),
locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`, as `A` is smooth over a field),
hence noetherian, and separated (`terminal.from A.X.left` factors as `A.X.hom` followed by the
separated map from the affine scheme `Spec k`). The dimension statement gives
`topologicalKrullDim A.X.left ≤ g`, and the vanishing statement with `d = g`, `n = g + 1` and the
quasi-coherent structure sheaf (`CechDegreeOne.isQuasicoherent_unit`) gives the vanishing.

## Provenance

See `Langlands.AlgebraicGeometry.CechH1Bound` for the mathematical route and its relation to the
registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, (6.12)–(6.15).
