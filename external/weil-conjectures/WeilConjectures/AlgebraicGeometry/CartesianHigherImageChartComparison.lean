/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartSystem
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeNaturality

/-! # Chart cohomology and cartesian exchange

Source: Stacks Project, Tag 0EYM, second proof, canonical cohomology comparisons.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable local instance (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

/-- Restricted chart cohomology compares with cartesian derived Hom, compatibly
with the prescribed exchange map. This is a map comparison, without continuity,
representatives, a limiting cone, affineness, qcqs hypotheses or filteredness.
Source: Stacks Project, Tags 0EYM (the square in the second proof), 03Q8
(higher-direct-image evaluation), 03CB (inverse-image composition) and 09YQ
(canonical cohomology maps).
(blueprint: lem-sc-cartesian-higher-image-chart-comparison).

Proof: Write S_i for D(i), X_i for X times_S S_i and p_i:X_i -> S_i.
The source of chart stage j is S_j times_{S_i} X_i. Pullback pasting identifies
it with X times_S S_j, preserving its maps to X and S_j. The analogous
identification at the cone point identifies S_limit times_{S_i} X_i with
X times_S S_limit. The test object U is the pullback of V along the i-th cone
leg, by hr. Pasting identifies V times_{S_i} the apex chart with U times_{S_limit}
(X times_S S_limit). Inverse-image composition identifies their restricted
coefficient sheaves. Derived adjunction for p_limit, together with the shift
comparison of R p_limit,* and the single-complex comparison of exact inverse
image, identifies the displayed derived Hom with raw Hom out of
p_limit^* Z[U]. The free abelian sheaf and etale restriction adjunction identifies
this raw Hom with cohomology of the coefficient on the last fibre product
(rawRestrictedCohomologyComparison). This gives e.
For j, the same construction identifies the chart cohomology with raw derived
Hom over S_j, evaluated on V times_{S_i} S_j. Pull the resulting class back along
the j-th cone leg. The canonical free-representable pullback comparison and hr
identify its source with Z[U][0]; the single-complex and shift comparisons give
lift j. For the compatibility equation, take the p_limit derived adjoint of
both sides. The exchange map is the mate of the inverse-image composition
comparison, so its counit cancels with the adjunction unit. The remaining map
is derived inverse image of the class followed by its coefficient comparison.
Naturality of rawRestrictedCohomologyComparison identifies this with the
canonical rawAffineComplexPullback and coefficient map that define
restrictedOverCohomologyMap. Pullback uniqueness identifies all geometric arrows,
and upperStarComp associativity identifies the coefficient comparisons.
Thus both sides give the same adjunct. This proves the equation independently
of invertibility of exchange. The same identities hold for empty charts and
q=0; no proper base change assertion is used. -/
theorem exists_cartesianChart_cohomology_comparison
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom (c.π.app i).left) :
    let h := pullback.snd f (D.obj i).hom
    let Fᵢ := (upperStar AddCommGrpCat.{u + 1} (pullback.fst f (D.obj i).hom)).obj F
    let E := cartesianChartDiagram f D i
    let d := cartesianChartCone f D c i
    ∃ (e : restrictedOverCohomology h Fᵢ (q : ℤ) d.pt V ≅ AddCommGrpCat.of
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree c.pt.left).obj U) ⟶
            (cartesianDerivedImage f c.pt.hom
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧))
      (lift : ∀ j : Over i, restrictedOverCohomology h Fᵢ (q : ℤ) (E.obj j) V →
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree c.pt.left).obj U) ⟶
            ((D+(((c.π.app j.left).left)^*[AddCommGrpCat.{u + 1}])).obj
              (cartesianDerivedImage f (D.obj j.left).hom
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)),
      ∀ (j : Over i) (x : restrictedOverCohomology h Fᵢ (q : ℤ) (E.obj j) V),
        lift j x ≫ (shiftFunctor _ (q : ℤ)).map
          (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
            (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
          e.hom (restrictedOverCohomologyMap h Fᵢ (q : ℤ) (d.π.app j) V x) := by
  refine ⟨cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr,
    cartesianChartCohomologyLift f D c F q i V U r hr, ?_⟩
  intro j x
  exact cartesianChartCohomologyLift_exchange f D c F q i V U r hr j x

end AlgebraicGeometry.Etale
