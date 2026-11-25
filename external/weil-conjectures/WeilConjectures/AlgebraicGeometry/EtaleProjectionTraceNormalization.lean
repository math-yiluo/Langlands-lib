/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit

/-! # Projection naturality followed by a scalar trace

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u'
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open MonoidalCategory in
private theorem projection_trace
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) (t : N ⟶ 𝟙_ _) :
    ((rightDerivedLowerStarProjectionMap C f).app M).app N ≫
        (lowerStar C f).rightDerivedFunctor.map
          (((derivedTensor C X).obj M).map
              ((upperStar C f).leftDerivedFunctor.map t ≫
                (leftDerivedUpperStarUnitIso C f).hom) ≫
            (derivedTensorRightUnitor C X M).hom) =
      ((derivedTensor C Y).obj ((lowerStar C f).rightDerivedFunctor.obj M)).map t ≫
        (derivedTensorRightUnitor C Y ((lowerStar C f).rightDerivedFunctor.obj M)).hom := by
  change ((rightDerivedLowerStarProjectionMap C f).app M).app N ≫
      (lowerStar C f).rightDerivedFunctor.map
        (M ◁ ((upperStar C f).leftDerivedFunctor.map t ≫
          (leftDerivedUpperStarUnitIso C f).hom) ≫ (ρ_ M).hom) =
    (lowerStar C f).rightDerivedFunctor.obj M ◁ t ≫
      (ρ_ ((lowerStar C f).rightDerivedFunctor.obj M)).hom
  let := leftDerivedUpperStarOplaxMonoidal C f
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η C f
  have hu := Adjunction.rightAdjointProjectionMap_app_app_tensorUnit
    (derivedUpperStarLowerStarAdjunction C f) (leftDerivedUpperStarTensorComparison C f)
    (fun _ _ ↦ rfl) M
  have hn := ((rightDerivedLowerStarProjectionMap C f).app M).naturality t
  change _ ◁ t ≫ ((rightDerivedLowerStarProjectionMap C f).app M).app (𝟙_ _) =
    ((rightDerivedLowerStarProjectionMap C f).app M).app N ≫
      (lowerStar C f).rightDerivedFunctor.map
        (M ◁ (upperStar C f).leftDerivedFunctor.map t) at hn
  change ((rightDerivedLowerStarProjectionMap C f).app M).app (𝟙_ _) = _ at hu
  have hi : inv (Functor.OplaxMonoidal.η (upperStar C f).leftDerivedFunctor) =
      (leftDerivedUpperStarUnitIso C f).inv := by
    apply (cancel_mono (leftDerivedUpperStarUnitIso C f).hom).1
    calc
      inv (Functor.OplaxMonoidal.η (upperStar C f).leftDerivedFunctor) ≫
          (leftDerivedUpperStarUnitIso C f).hom = 𝟙 _ := by
        rw [← leftDerivedUpperStarOplaxMonoidal_η C f, IsIso.inv_hom_id]
      _ = _ := (leftDerivedUpperStarUnitIso C f).inv_hom_id.symm
  rw [hi] at hu
  rw [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, ← Category.assoc, ← hn, Category.assoc, hu]
  simp only [Category.assoc, ← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Naturality and unit normalization of the ordinary projection mate.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle;
Stacks Tag 0B56, projection-formula map.
(auxiliary; not a blueprint node).

Proof: apply naturality in the second argument of rightDerivedLowerStarProjectionMap
to t:N→A_Y. It reduces the composite to tensoring t with the identity on Rf*M,
followed by projection at the tensor unit, then Rf* of identity tensor the pullback
unit comparison and the right unitor. The tensor-unit projection is the right unitor
followed by Rf* of the inverse right unitor and inverse pullback-unit comparison,
by rightAdjointProjectionMap_app_app_tensorUnit. The pullback oplax unit is the
specified leftDerivedUpperStarUnitIso by its normalization on degree-zero complexes.
The inverse unit comparison and the two right unitors cancel inside Rf*. The remaining
map is precisely identity tensor t followed by the right unitor. This calculation needs
no properness or coefficient finiteness. -/
theorem projectionTraceNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategoryModule A X) (N : DerivedCategoryModule A Y)
    (t : N ⟶ constantComplex A Y) :
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app N ≫
        (push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              ((pull A f).map t ≫
                (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom) ≫
            (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((push A f).obj M)).map t ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y ((push A f).obj M)).hom := by
  exact projection_trace (ModuleCat.{u + 1} A) f M N t

end AlgebraicGeometry.Etale.CoordinateTrace
