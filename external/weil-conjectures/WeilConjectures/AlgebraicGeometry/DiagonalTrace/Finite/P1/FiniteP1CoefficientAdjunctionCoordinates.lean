/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1CoefficientCoordinateDefinitions
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1AdjunctionTransport
import WeilConjectures.AlgebraicGeometry.SpTowerP1.FiniteP1CoefficientExistence
import WeilConjectures.SixFunctors.Finite.FiniteP1UnitAdjustment
import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
import Mathlib.AlgebraicGeometry.Scheme

/-! # Finite coefficient and adjunction coordinates

Source: blueprint latest, diagonal-tower trace proof (1), identification of
finite coefficient units and direct images before the Chern-class calculation.
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def finiteGeoUnitIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) :
    geoP1Unit A T ≅ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} A))) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).app
      (Etale.ordinaryFiniteConstant A T) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (Functor.OplaxMonoidal.η (comparisonUpperStar (ModuleCat.{u + 1} A) T))) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

attribute [local irreducible] finiteNativePullCoordinate finiteProjectionPullCoordinate
  finiteGeoUnitIso finiteUnitCoordinate finiteOverUnitCoordinate

/-- Finite coordinate comparisons preserve the ordinary adjunction and the
normalized coefficient pullback. This statement contains no Chern class.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), finite unit and direct-image
identifications; `sk-prop-sp-tower-geometric-p1.proof.md`, Levels.
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates).

Proof: the constant-module and root-tensor universal properties construct
normalized coefficient coordinates on S and X. Invertibility of the exponent
pulls back along f. Uniqueness of the intrinsic inverse-image adjoint and
composition with the isomorphism e give an initial comparison p0. Its value on
the coefficient unit may differ from the evaluated coefficient pullback by an
automorphism of H(geoP1Unit). Since H is an equivalence, lift this discrepancy
to the ordinary projective-line category. The coefficient unit is its tensor
unit, so tensoring this automorphism with every object and conjugating by
unitors extends it to a natural automorphism. Adjust p0 by this automorphism
to get p with exactly the displayed coefficient equation. The invertible mate
of p gives q, and the mate unit identity gives the first equation for every
object. This uses only the given coefficient isomorphism, not an additional
normalization theorem for a fixed choice of p. Empty schemes, the zero ring,
and n=0 are included in the same categorical and tensor arguments. -/
theorem finiteP1_coefficient_adjunction_coordinates
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (b : SpTowerShriek.Base l E) {f : X ⟶ S}
    (e : X ≅ ProjectiveLine S) (he : e.hom ≫ (ProjectiveLine S ↘ S) = f)
    (g : SpTowerShriek.Geometry l E b f) (cp : CoefficientPullback l E b f g)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    let A := FiniteRing l E n
    let F := (Scheme.sfIntrinsicModuleEquivalence S
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory
    let H := finiteOverRealization l E n e
    let L := Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f
    let R := (Scheme.proEtaleConstantRingPushforward
      (SpTowerShriek.R l E n) f).rightDerivedFunctor
    let ad := (Scheme.proEtaleConstantRingAdjunction
      (SpTowerShriek.R l E n) f).mapDerivedCategoryRightDerivedAdjunction
    let ap := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)
    ∃ (hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
      (cX : SpTowerP1.CoefficientCoordinates l E n X hX)
      (cS : SpTowerP1.CoefficientCoordinates l E n S
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))
      (p : F ⋙ L ≅ geoP1Pullback A (ProjectiveLine S ↘ S) ⋙ H)
      (q : H ⋙ R ≅ geoP1Pushforward A (ProjectiveLine S ↘ S) ⋙ F),
      (∀ M, ad.unit.app (F.obj M) ≫ R.map (p.hom.app M) ≫
        q.hom.app ((geoP1Pullback A (ProjectiveLine S ↘ S)).obj M) = F.map (ap.unit.app M)) ∧
      ((g.pullEvaluation n).inv.app (unit S (Arings l E S)) ≫
        (SpTowerShriek.Ev l E X n).map (cp.derivedIso l E).hom ≫
        (finiteOverUnitCoordinate l E n e cX).hom =
      L.map (finiteUnitCoordinate l E n S cS).hom ≫ p.hom.app (geoP1Unit A S) ≫
        H.map (geoP1UnitPullback A (ProjectiveLine S ↘ S)).hom)  := by
  let hS' : IsUnit ((l ^ (n + 1) : ℕ) : Γ(S, ⊤)) := by
    simpa only [Nat.cast_pow] using hS.pow (n + 1)
  have hX := finiteP1_unitOnPullback (l ^ (n + 1)) f hS'
  let cX := SpTowerP1.finiteP1CoefficientCoordinates l E n X hX
  let cS := SpTowerP1.finiteP1CoefficientCoordinates l E n S hS'
  let F := (Scheme.sfIntrinsicModuleEquivalence S
    (SpTowerShriek.R l E n)).functor.mapDerivedCategory
  let H := finiteOverRealization l E n e
  let L := Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f
  let P := geoP1Pullback (FiniteRing l E n) (ProjectiveLine S ↘ S)
  let U := geoP1Unit (FiniteRing l E n) S
  let V := geoP1Unit (FiniteRing l E n) (ProjectiveLine S)
  let i := geoP1UnitPullback (FiniteRing l E n) (ProjectiveLine S ↘ S)
  let p0 := finiteProjectionPullCoordinate (SpTowerShriek.R l E n) e he
  let u : L.obj (F.obj U) ≅ H.obj V :=
    L.mapIso (finiteUnitCoordinate l E n S cS).symm ≪≫
      (g.pullEvaluation n).symm.app (unit S (Arings l E S)) ≪≫
      (SpTowerShriek.Ev l E X n).mapIso (cp.derivedIso l E) ≪≫
      finiteOverUnitCoordinate l E n e cX
  have : H.IsEquivalence := by
    have : (upperStar (ModuleCat.{u + 1} (FiniteRing l E n)) e.hom).IsEquivalence :=
      inferInstance
    have : (geoP1Pullback (FiniteRing l E n) e.hom).IsEquivalence :=
      Functor.isEquivalence_of_iso
        (leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (FiniteRing l E n)) e.hom).symm
    exact inferInstanceAs
      (geoP1Pullback (FiniteRing l E n) e.hom ⋙
        (Scheme.sfIntrinsicModuleEquivalence X
          (SpTowerShriek.R l E n)).functor.mapDerivedCategory).IsEquivalence
  obtain ⟨p, hp⟩ := finiteP1_adjust_coordinate_unit (F ⋙ L) P H p0 U V
    (finiteGeoUnitIso (FiniteRing l E n) (ProjectiveLine S)) i u
  have : F.IsEquivalence := by
    exact inferInstanceAs (Scheme.sfIntrinsicModuleEquivalence S
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory.IsEquivalence
  let hq0 := finiteAdjunctionCoordinates
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (FiniteRing l E n)) (ProjectiveLine S ↘ S))
    (Scheme.proEtaleConstantRingAdjunction
      (SpTowerShriek.R l E n) f).mapDerivedCategoryRightDerivedAdjunction F H p
  let q := Classical.choose hq0
  have hq := Classical.choose_spec hq0
  refine ⟨hX, cX, cS, p, q, hq, ?_⟩
  symm
  change L.map (finiteUnitCoordinate l E n S cS).hom ≫ p.hom.app U ≫ H.map i.hom = _
  rw [hp]
  dsimp only [u, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ← L.map_comp, Iso.hom_inv_id, L.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.DiagonalTrace
