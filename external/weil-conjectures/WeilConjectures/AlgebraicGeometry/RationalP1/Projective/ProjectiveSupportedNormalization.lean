/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar

-- Generalize the composite before eliminating its equality to the identity. This
-- keeps the intermediate module and sheaf object types aligned without unfolding sites.
omit [IsCommMonObj Λ] in
private theorem composition_hom_heq {P W : Scheme.{u}} (k : P ⟶ W) (f : W ⟶ P)
    (M : Modules Λ P) (g : P ⟶ P) (h : g = 𝟙 P)
    (i : CondensedRing.lowerStar Λ k ⋙ CondensedRing.lowerStar Λ f ≅
      CondensedRing.lowerStar Λ g)
    (j : ProEtale.lowerStar Ab.{u + 1} k ⋙ ProEtale.lowerStar Ab.{u + 1} f ≅
      ProEtale.lowerStar Ab.{u + 1} g)
    (hij : HEq (i.hom.app M).hom (j.hom.app M.X)) :
    HEq ((i ≪≫ CondensedRing.lowerStarCongr Λ h ≪≫
        CondensedRing.lowerStarId Λ P).hom.app M).hom
      ((j ≪≫ ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
        ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X) := by
  subst g
  have hij' := eq_of_heq hij
  have hid : ((CondensedRing.lowerStarId Λ P).hom.app M).hom =
      (ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X := rfl
  apply heq_of_eq
  simpa only [Iso.trans_hom, NatTrans.comp_app, Mod.comp_hom',
    CondensedRing.lowerStarCongr_hom_app_hom, hid]
    using congrArg (fun t ↦ t ≫ (ProEtale.lowerStarCongr Ab.{u + 1} (rfl : 𝟙 P = 𝟙 P)).hom.app
      M.X ≫ (ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X) hij'

-- Check the carrier calculation before specializing to the concrete projective line.
omit [IsCommMonObj Λ] in
private theorem supported_normalization {P W : Scheme.{u}} (k : P ⟶ W) (f : W ⟶ P)
    (M : Modules Λ P) (h : k ≫ f = 𝟙 P)
    (s : M ≅ (CondensedRing.lowerStar Λ f).obj ((CondensedRing.lowerStar Λ k).obj M))
    (hs : HEq s.inv.hom
      ((ProEtale.lowerStarComp Ab.{u + 1} k f ≪≫
        ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
          ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X)) :
    s.inv = (CondensedRing.lowerStarComp Λ k f ≪≫
      CondensedRing.lowerStarCongr Λ h ≪≫ CondensedRing.lowerStarId Λ P).hom.app M := by
  apply Mod.hom_ext
  have hc := composition_hom_heq Λ k f M _ h
    (CondensedRing.lowerStarComp Λ k f) (ProEtale.lowerStarComp Ab.{u + 1} k f)
    (heq_of_eq (CondensedRing.lowerStarComp_hom_app_hom Λ k f M))
  exact eq_of_heq (hs.trans hc.symm)

-- Preserve the existing commutative-coefficient parameter of the public theorem.
set_option linter.unusedSectionVars false in
/--
The inverse support isomorphism is the normalized lower-star composite,
congruence, and identity comparison on the regular module.
-/
theorem projective_supported_normalization (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    d.support₂.iso.inv =
      (CondensedRing.lowerStarComp Λ (diagonalImmersion Y) (secondProjection Y) ≪≫
        CondensedRing.lowerStarCongr Λ d.support₂.over_eq ≪≫
          CondensedRing.lowerStarId Λ (ProjectiveLine Y)).hom.app
            (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) := by
  exact supported_normalization Λ (diagonalImmersion Y) (secondProjection Y)
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) d.support₂.over_eq
    d.support₂.iso d.support₂.normalization

end AlgebraicGeometry.ProEtale.RationalP1
