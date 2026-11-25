/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
/-!
# Degree-zero constant coefficients under connected fibres

## References

* Stacks Project, Tag 0A3H, applied over every etale base object
* Tag 0GKV, case (b), degree zero
* Stacks Project, Tags 0A3H and 0GKV, case (b), degree zero
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private theorem connected_unit_isIso
    {X S : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (f : X ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G) := by
  have h : IsIso
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G).hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    let W : X.Etale :=
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj U.unop
    have : Flat ((𝟙 W : W ⟶ W).left ≫ pullback.fst U.unop.hom f) := by
      change Flat (𝟙 _ ≫ pullback.fst U.unop.hom f)
      rw [Category.id_comp]
      infer_instance
    have : QuasiCompact ((𝟙 W : W ⟶ W).left ≫ pullback.fst U.unop.hom f) := by
      change QuasiCompact (𝟙 _ ≫ pullback.fst U.unop.hom f)
      rw [Category.id_comp]
      infer_instance
    have : GeometricallyConnected ((𝟙 W : W ⟶ W).left ≫ pullback.fst U.unop.hom f) := by
      change GeometricallyConnected (𝟙 _ ≫ pullback.fst U.unop.hom f)
      rw [Category.id_comp]
      infer_instance
    have h := isIso_upperStarSectionsMap R f G (𝟙 W)
    change IsIso ((((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G).hom.app
      (op U.unop)) ≫ ((upperStar (ModuleCat.{u + 1} R) f).obj G).obj.map (𝟙 W).op) at h
    exact IsIso.of_isIso_comp_right
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G).hom.app U)
      (((upperStar (ModuleCat.{u + 1} R) f).obj G).obj.map (𝟙 W).op)
  have : IsIso ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G)) := h
  exact isIso_of_reflects_iso _
    (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))

private theorem constant_finiteLocallyConstant
    (S : Scheme.{u}) {R : Type (u + 1)} [CommRing R]
    (M : ModuleCat.{u + 1} R) [Finite M] :
    Scheme.IsFiniteLocallyConstantSheaf
      ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  let G := (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  have : Scheme.IsLocallyConstantSheaf G :=
    (Sheaf.isConstant_of_iso _ (Iso.refl G)).isLocallyConstantSheaf
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Scheme.IsFiniteSheaf G := by
    constructor
    intro Ω _ _ s
    let e := (Scheme.pointSmallEtale s).sheafFiberConstantSheafIso M
    have : Finite (((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj G) :=
      Finite.of_equiv M e.toLinearEquiv.toEquiv.symm
    exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite (R := R))
  exact {}

/-- Degree-zero direct image of finite constant coefficients is constructible under
a flat quasi-compact morphism with geometrically connected nonempty fibres. -/
theorem higherDirectImage_zero_constant_constructible
    {X S : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (f : X ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f]
    (M : ModuleCat.{u + 1} R) [Finite M] :
    Scheme.IsConstructibleSheaf (higherDirectImage R f 0
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) := by
  let GS := (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  let GX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  have := connected_unit_isIso f GS
  let L := lowerStar (ModuleCat.{u + 1} R) f
  let e : higherDirectImage R f 0 GX ≅ GS :=
    (L.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).app GX ≪≫
      ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedZeroIsoSelf).app GX ≪≫
      (lowerStar (ModuleCat.{u + 1} R) f).mapIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} R) f).app M).symm ≪≫
      (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app GS)).symm
  have := constant_finiteLocallyConstant S M
  have := Scheme.IsFiniteLocallyConstantSheaf.of_iso e.symm
  exact ⟨Scheme.Stratification.trivial S, fun _ ↦
    Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 S) _⟩
end AlgebraicGeometry.Etale
