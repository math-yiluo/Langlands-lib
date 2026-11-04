import Langlands.AlgebraicGeometry.LinearSystem.RelativeLinearActionTwist
import Langlands.AlgebraicGeometry.Modules.UnitAutomorphisms

/-! # Scalar linear actions on the actual degree-one twist -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- The existing unit action, evaluated on global sections. -/
@[simp]
lemma unitAut_hom_app_top {X : Scheme.{u}} (M : X.Modules) (c : Γ(X, ⊤)ˣ)
    (m : GlobalSections M) :
    (unitAut M c).hom.app ⊤ m = (c : Γ(X, ⊤)) • m := by
  rw [unitAut_hom_app]
  change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) (c : Γ(X, ⊤)) • m = _
  simp

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [CommRing K] {X S : Scheme.{u}} {n : ℕ}

/-- Equality transport to the identity pullback, followed by the existing unit action. -/
def identityScalarPullbackIso {X : Scheme.{u}} (M : X.Modules)
    (f : X ⟶ X) (w : f = 𝟙 X) (c : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pullback f).obj M ≅ M :=
  (Scheme.Modules.pullbackCongr w).app M ≪≫
    (Scheme.Modules.pullbackId X).app M ≪≫ Scheme.Modules.unitAut M c

/-- The canonical comparison over an identity scheme map, followed by a unit
scalar, has the expected coordinate formula. -/
lemma pullback_identity_scalar_coordinate {X : Scheme.{u}} (M : X.Modules)
    (f : X ⟶ X) (w : f = 𝟙 X) (c : Γ(X, ⊤)ˣ) (s : GlobalSections M) :
    (identityScalarPullbackIso M f w c).hom.app ⊤
        (pullbackSection f M s) = (c : Γ(X, ⊤)) • s := by
  change (Scheme.Modules.unitAut M c).hom.app ⊤
    (((Scheme.Modules.pullbackId X).hom.app M).app ⊤
      (((Scheme.Modules.pullbackCongr w).hom.app M).app ⊤
        (pullbackSection f M s))) = _
  rw [pullbackCongr_coordinate, pullbackId_coordinate, unitAut_hom_app_top]

/-- A scalar formula on covering frames identifies the actual pullback comparison. -/
lemma pullback_comparison_scalar {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (f : X ⟶ X) (w : f = 𝟙 X) (c : Γ(X, ⊤)ˣ)
    (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (hα : ∀ i, α.hom.app ⊤ (pullbackSection f M (s i)) = (c : Γ(X, ⊤)) • s i) :
    α = identityScalarPullbackIso M f w c := by
  apply Iso.ext
  apply hom_ext_of_generating_sections _ (frameCover_pullback hM s hs f)
  intro i
  exact (hα i).trans (pullback_identity_scalar_coordinate M f w c (s i)).symm

lemma linearChangeSections_smulOfUnit (p : X ⟶ Spec (CommRingCat.of K))
    {L : LineBundle X} (s : Fin (n + 1) → GlobalSections L.obj) (c : Kˣ)
    (i : Fin (n + 1)) :
    linearChangeSections p s (LinearEquiv.smulOfUnit c).toLinearMap i =
      Scheme.Modules.scalarsFromBase p (c : K) • s i := by
  classical
  change (∑ j, Scheme.Modules.scalarsFromBase p
    ((c : K) * (Pi.single j (1 : K) : Fin (n + 1) → K) i) • s j) = _
  simp [Pi.single_apply, apply_ite, ite_smul]

/-- The scalar matrix retains its scalar on the degree-one line bundle,
after its scheme action is identified with the identity. -/
lemma relativeLinearActionTwistIso_smulOfUnit
    (a : S ⟶ Spec (CommRingCat.of K)) (c : Kˣ) :
    relativeLinearActionTwistIso (n := n) a (LinearEquiv.smulOfUnit c) =
      (Scheme.Modules.pullbackCongr
        (RelativeProjectiveSpace.linearAction_smulOfUnit a c)).app
          (RelativeProjectiveSpace.twistOne S n).obj ≪≫
        (Scheme.Modules.pullbackId (RelativeProjectiveSpace S n)).app
          (RelativeProjectiveSpace.twistOne S n).obj ≪≫
        Scheme.Modules.unitAut (RelativeProjectiveSpace.twistOne S n).obj
          (Units.map (Scheme.Modules.scalarsFromBase
            (RelativeProjectiveSpace.toBase S n ≫ a)).toMonoidHom c) := by
  apply pullback_comparison_scalar (RelativeProjectiveSpace.twistOne S n).property
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (isOpenCover_trivializationOpen
      (relativeProjectiveCoordinates_generate S n))
  intro i
  rw [relativeLinearActionTwistIso_coordinate]
  change linearChangeSections (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (LinearEquiv.smulOfUnit c).toLinearMap i = _
  exact linearChangeSections_smulOfUnit _ _ c i

end Langlands.AlgebraicGeometry.LinearSystem
