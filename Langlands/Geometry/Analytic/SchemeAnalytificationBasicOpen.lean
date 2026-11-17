import Langlands.Geometry.Analytic.AnalytificationCenter
import Mathlib.RingTheory.Localization.Basic

/-! # Localization of affine-open coordinate rings -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.CenterRange

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

section Algebraic

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) (g : Γ(X, U.val))

/-- A section on an affine open regarded as an element of its coordinate algebra. -/
def basicOpenGenerator : CoordinateRing (structureMap f U) :=
  (U : X.Opens).topIso.inv g

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to a principal affine open is localization of the actual coordinate rings. -/
theorem isLocalization_restriction_basicOpen :
    letI := (restriction f (X.affineBasicOpen_le g)).toRingHom.toAlgebra
    IsLocalization.Away (basicOpenGenerator f U g)
      (CoordinateRing (structureMap f (X.affineBasicOpen g))) := by
  let W : X.affineOpens := X.affineBasicOpen g
  let h : (W : X.Opens) ≤ U := X.affineBasicOpen_le g
  let := (restriction f h).toRingHom.toAlgebra
  let eU : CoordinateRing (structureMap f U) ≃+* Γ(X, U.val) :=
    (U : X.Opens).topIso.commRingCatIsoToRingEquiv
  let eW : CoordinateRing (structureMap f W) ≃+* Γ(X, X.basicOpen g) :=
    (W : X.Opens).topIso.commRingCatIsoToRingEquiv
  let := (eW.toRingHom.comp (restriction f h).toRingHom).toAlgebra
  apply (IsLocalization.isLocalization_iff_of_ringEquiv
    (Submonoid.powers (eU.symm g)) eW).mpr
  let := U.property.isLocalization_basicOpen g
  apply IsLocalization.of_ringEquiv_left eU
    (show (Submonoid.powers (eU.symm g)).map eU = Submonoid.powers g by
      rw [Submonoid.map_powers, eU.apply_symm_apply])
  intro a
  have compat : (X.homOfLE h).appTop ≫ (W : X.Opens).topIso.hom =
      (U : X.Opens).topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
    rw [Scheme.homOfLE_appTop]
    simp only [Scheme.Opens.topIso_hom, ← Functor.map_comp, ← op_comp]
    rfl
  exact ConcreteCategory.congr_hom compat a

end Algebraic

end Langlands.Analytic.SchemeAnalytification.CenterRange
