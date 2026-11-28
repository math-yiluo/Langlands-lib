# Proof of the existence of smoothenings over discrete valuation rings

`Langlands.AlgebraicGeometry.dvrSmootheningStatement.{u}` proves the Library proposition
`Langlands.AlgebraicGeometry.DvrSmootheningStatement.{u}`, imported from
`Langlands.AlgebraicGeometry.DvrSmootheningStatement`. Its type is exactly that closed proposition.

```lean
theorem dvrSmootheningStatement : DvrSmootheningStatement.{u}
```

## Statement proved

Let `R` be a discrete valuation ring with fraction field `K` and `f : X ⟶ Spec R` locally of finite
type and quasi-compact with smooth generic fibre. Then there is a proper morphism `g : X' ⟶ X`
which is an isomorphism on generic fibres such that every point `a : Spec R' ⟶ X` over `Spec R`,
where `R'` is a discrete valuation ring with a local map `R → R'` of ramification index one
(`IsRamificationIndexOne`), lifts through an open `U ⊆ X'` on which `g ≫ f` is smooth.

## Proof

```lean
theorem dvrSmootheningStatement : DvrSmootheningStatement.{u} :=
  DvrSmoothening.dvrSmoothening_of DvrSmoothening.defectZeroSmoothAtStatement
    DvrSmoothening.dilatationDefectStatement DvrSmoothening.goodChartStatement
    DvrSmoothening.defectBoundStatement blowupChartStatement
```

`DvrSmoothening.dvrSmoothening_of` (module `Langlands.AlgebraicGeometry.DvrSmoothening.Reduction`)
derives the statement from five propositions, each proved in its own module:

| Proposition | Proof | Source (BLR) |
| --- | --- | --- |
| `DvrSmoothening.DefectZeroSmoothAtStatement` | `DvrSmoothening.defectZeroSmoothAtStatement` (`DvrSmoothening.DefectZero`) | §3.3, Lemma 1 |
| `DvrSmoothening.DefectBoundStatement` | `DvrSmoothening.defectBoundStatement` (`DvrSmoothening.DefectBound`) | §3.3, Proposition 3 |
| `DvrSmoothening.GoodChartStatement` | `DvrSmoothening.goodChartStatement` (`DvrSmoothening.GoodChart`) | §3.3, Lemma 4; §3.4 |
| `DvrSmoothening.DilatationDefectStatement` | `DvrSmoothening.dilatationDefectStatement` (`DvrSmoothening.DilatationDefect`) | §3.3, Proposition 5; §3.6 |
| `BlowupChartStatement` | `blowupChartStatement` (`BlowupChartProof`) | Stacks, Section 31.33 |

The reduction runs the smoothening induction of BLR §3.4 (printed pp. 71–73) directly on the set of
all points with values in discrete valuation rings of ramification index one
(`DvrSmoothening.TestPoint`): a bound for their defects (`DefectBound`), then an outer induction on
this bound and, inside it, a noetherian induction on the centre, the closure of the closed points of
the non-smooth points (`DvrSmoothening.Induction`). In each step a good chart `D(s)` meeting the centre is chosen; the
points specializing outside `D(s)` (smaller centre) are resolved first by a modification which is
an isomorphism over `D(s)`; then the global centre of the family of lifts specializing over `D(s)`
is blown up on the modified scheme, using the good chart there. This blow-up strictly lowers the
defects of those lifts whose specializations lie in the centre (`DvrSmoothening.Step`), and only
these lifts are passed to the outer induction, which resolves them with the smaller bound. The
other lifts over `D(s)` specialize outside the centre, hence into the smooth locus; they are
already resolved, and stay resolved under the blow-up and the last modification, which are
isomorphisms away from the respective centres.

`dvrSmoothening_of` applies this to the family of all test points, after choosing a uniformizer and
deducing from the smooth generic fibre that all points over the generic point of `Spec R` are
smooth. The resulting proper `g` is an isomorphism away from the centre. The centre misses the
generic fibre, so `g` induces an isomorphism of generic fibres
(`isIso_pullback_map_of_range_subset`). Each test point lifts along `g` with closed point in the
smooth locus of `g ≫ f`. As every point of `Spec R'` specializes to the closed point, the lift
factors through that smooth locus, an open on which `g ≫ f` is smooth (`smooth_smoothLocus_ι`).

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Modules

`Langlands/AlgebraicGeometry/DvrSmoothening/`: `TorsionLength`, `DefectTransport`, `Charts`,
`Points`, `Centres`, `Modification`, `ChartLocalization`, `Step`, `Induction`, `Reduction`,
`DefectBound`, `GoodChartAlgebra`, `GoodChart`, `JacobianPoint`, `DefectZero`, `DilatationLattice`,
`DilatationPresentation`, `DilatationCentre`, `DilatationLocal`, `DilatationResidue`,
`DilatationRelations`, `DilatationDefect`; and `Langlands/AlgebraicGeometry/BlowupChartProof`.

Source: S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Springer 1990, §3.1, Theorem 3
(printed p. 61) and §3.6, Lemma 5 (printed p. 79, PDF p. 86), with Definition 1 of §3.6 (printed
p. 78), the results of §3.3 (printed pp. 64–71) and the induction of §3.4 (printed pp. 71–73).
