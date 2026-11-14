# The universal divisor of the linear system over a Grassmannian

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`., sub-namespace `LinSys`. Let `C` be a Čech representative of `L` (with frames) and
`D : Rep R C.Q 1` a representing scheme of the Grassmannian of rank-one quotients of `Q` (Library
`Module.Grassmannian.ProjectiveEmbedding.Rep`).

- `ptOf`, `pt_ptOf`: the quotient corresponding to a `B`-point of `D.Gr`.
- `InSomeChart D k`: `k` lands in some chart `D.V (fun _ => x)`; `inChart_ptOf`.
- `vOf`, `span_range_vOf`, `ptOf_comp`, `coord_congr`, `vOf_comp`: the chart coordinates
  `Q → B` of a chart point (`LineQuotientCoordinates.coord`), whose values generate the unit ideal,
  and their behaviour under base change (up to a unit).
- `FOf L D k hk hP := zeroIdeal σ_{vOf k}` and `FOf_comp` (naturality, by
  `zeroIdeal_comap_homEquivSections` and `zeroIdeal_homEquivSections_smul`).
- `pointIdeals`: these data form a `PointIdeals` family.
- `exists_universalDivisor`: an ideal sheaf `W` on `X ×_R D.Gr` with
  `W.comap (ptMap k) = FOf k` for every chart point `k`.

## Source

Kleiman, *The Picard scheme*, p.26 and Exercise 3.14: the universal divisor `W` on `X_{P(Q)}`,
the zero scheme of the section corresponding to the tautological quotient `Q_{P(Q)} → O(1)`; here
it is glued from the zero loci over the charts.
