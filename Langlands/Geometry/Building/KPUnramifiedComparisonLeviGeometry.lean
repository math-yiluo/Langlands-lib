import Langlands.Geometry.Building.KPUnramifiedApartmentLift
import Langlands.Geometry.Building.UnramifiedApartmentDescentTorsor
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Generic descended vectors and constant Levi-root valuations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance comparisonLeviGeometryAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

local notation "fK" =>
  CategoryTheory.Functor.map
    (CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))) t.f

set_option maxHeartbeats 1000000 in
/-- On an upstairs root, a generic integral downstairs cocharacter has zero
descended pairing exactly when the root restricts trivially to the downstairs
split torus. -/
theorem eval_descent_eq_zero_iff_of_generic
    (ξ : cocharacterLattice P.S) (hξ : IsGenericCocharacter P.i ξ)
    {b : characterLattice L.buildingData.S} (hb : b ∈ relativeRoots L.buildingData.i) :
    eval L.buildingData.S b
        (descentCocharacterMap F (UnramifiedClosure F) t.f
          P.isMaximalSplitTorus.isSplitSubtorus.1 ((1 : ℝ) ⊗ₜ[ℤ] ξ)) = 0 ↔
      fK ≫ b = 0 := by
  constructor
  · intro hzero
    by_contra hb0
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    have hfactor : CommGroupScheme.groupHom fK ≫ t.upstairsInclusion =
        (GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map P.i := by
      rw [← t.factor, Functor.map_comp]
      rfl
    have hroot : fK ≫ b ∈ relativeRoots
        ((GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map P.i) := by
      rw [← hfactor, mem_relativeRoots]
      rw [mem_relativeRoots] at hb
      refine ⟨hb0, fun hbot => hb.2 ?_⟩
      exact eq_bot_iff.2 ((weightSpace_le_comp _ _ b).trans hbot.le)
    obtain ⟨a, ha⟩ :=
      (P.isMaximalSplitTorus.isSplitSubtorus.1.characterLattice_baseChange_bijective
        (algebraBaseMap F (UnramifiedClosure F)) P.S).2 (fK ≫ b)
    have haR : a ∈ relativeRoots P.i := by
      have h := (mem_roots_baseChange_iff (K := UnramifiedClosure F) G P.S
        P.isMaximalSplitTorus.isSplitSubtorus.1 P.i a).1
      rw [ha] at h
      exact h hroot
    rw [eval_descentCocharacterMap, ← ha, eval_splitCocharacterBaseChange,
      eval_tmul, one_mul] at hzero
    apply hξ a haR
    exact_mod_cast hzero
  · intro hzero
    rw [eval_descentCocharacterMap, hzero, eval_zero_char]

set_option maxHeartbeats 2000000 in
/-- Every character trivial on the downstairs split torus has constant
valuation along the supplied Galois-fixed apartment lift. -/
theorem val_eq_of_restriction_zero (y y' : P.Apartment)
    (b : characterLattice L.buildingData.S) (hb : fK ≫ b = 0) :
    (L.e y).val b = (L.e y').val b := by
  obtain ⟨v, hv⟩ := unramified_exists_descent_vadd_of_galoisFixed
    P.isConnectedReductive P.isMaximalSplitTorus t.factor t.isMaximalSplitTorus
    L.apartment (L.e y) (L.e y') (L.fixed y) (L.fixed y')
  funext g
  rw [hv, RootFunctionFamily.vadd_apply, eval_descentCocharacterMap, hb, eval_zero_char]
  simp

/-- The upstairs roots of the pairing Levi of a generic descended vector
have constant valuations along the lift. -/
theorem val_eq_on_zeroPairingRoots_of_generic
    (ξ : cocharacterLattice P.S) (hξ : IsGenericCocharacter P.i ξ)
    (y y' : P.Apartment) (b : characterLattice L.buildingData.S)
    (hb : b ∈ L.buildingData.zeroPairingRoots
      (descentCocharacterMap F (UnramifiedClosure F) t.f
        P.isMaximalSplitTorus.isSplitSubtorus.1 ((1 : ℝ) ⊗ₜ[ℤ] ξ))) :
    (L.e y).val b = (L.e y').val b :=
  L.val_eq_of_restriction_zero y y' b
    ((L.eval_descent_eq_zero_iff_of_generic ξ hξ hb.1).1 hb.2)

set_option maxHeartbeats 1000000 in
/-- There is an integral downstairs cocharacter whose descended vector has
precisely the zero-restriction roots as its pairing Levi roots, with constant
valuations along the lift. -/
theorem exists_generic_levi_geometry :
    ∃ ξ : cocharacterLattice P.S, IsGenericCocharacter P.i ξ ∧
      ∀ (y y' : P.Apartment), ∀ b ∈ L.buildingData.zeroPairingRoots
        (descentCocharacterMap F (UnramifiedClosure F) t.f
          P.isMaximalSplitTorus.isSplitSubtorus.1 ((1 : ℝ) ⊗ₜ[ℤ] ξ)),
        (L.e y).val b = (L.e y').val b := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨ξ, hξ⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  exact ⟨ξ, hξ, L.val_eq_on_zeroPairingRoots_of_generic ξ hξ⟩

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
