import Langlands.GroupScheme.IdentityJetAffineGenerators

/-! # Actual affine test points of identity jets -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

private theorem specTop_fromSpec (B : CommRingCat.{u}) :
    (isAffineOpen_top (Spec B)).fromSpec = Spec.map (Scheme.ΓSpecIso B).inv := by
  rw [IsAffineOpen.fromSpec_top]
  apply (cancel_mono (Spec B).toSpecΓ).mp
  change (Spec B).isoSpec.inv ≫ (Spec B).isoSpec.hom = _
  rw [Iso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]

/-- The spectrum of the actual coordinate-function map is its actual affine test point. -/
theorem spec_coordinateMap {X : Scheme.{u}} {B : CommRingCat.{u}}
    (j : X ⟶ Spec B) (V : X.Opens) (hV : IsAffineOpen V) :
    Spec.map (CommRingCat.ofHom
      ((j.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso B).inv.hom)) =
      hV.fromSpec ≫ j := by
  change Spec.map ((Scheme.ΓSpecIso B).inv ≫ j.appLE ⊤ V (by simp)) = _
  rw [Spec.map_comp, ← specTop_fromSpec]
  exact IsAffineOpen.SpecMap_appLE_fromSpec j (isAffineOpen_top (Spec B)) hV (by simp)

variable {S : Scheme.{u}} (H : GroupScheme S) [IsAffineHom H.X.hom]

private theorem projection_affine (n : ℕ) : IsAffineHom (projection H n) := by
  let : IsClosedImmersion (inclusion H n) := by
    change IsClosedImmersion (ideal H n).subschemeι
    infer_instance
  change IsAffineHom (inclusion H n ≫ H.X.hom)
  infer_instance

attribute [local instance] projection_affine

/-- The actual identity jet above an affine base open is affine. -/
theorem isAffineOpen_jetPreimage (n : ℕ) (U : S.affineOpens) :
    IsAffineOpen (projection H n ⁻¹ᵁ U) := U.2.preimage (projection H n)

/-- The ambient coordinate map on actual jet functions classifies its actual affine point. -/
theorem spec_jetCoordinateMap {B : CommRingCat.{u}} (j : H.X.left ⟶ Spec B)
    (n : ℕ) (U : S.affineOpens) :
    Spec.map (CommRingCat.ofHom (jetCoordinateMap H j n U)) =
      (isAffineOpen_jetPreimage H n U).fromSpec ≫ inclusion H n ≫ j := by
  exact (spec_coordinateMap (inclusion H n ≫ j)
    (projection H n ⁻¹ᵁ U) (isAffineOpen_jetPreimage H n U)).trans (Category.assoc _ _ _)

open Corepresented

variable {R : CommRingCat.{u}} (F : CommAlgCat R ⥤ GrpCat.{u})
  {B : CommAlgCat R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (b : S ⟶ Spec R) (j : H.X.left ⟶ Spec (CommRingCat.of B))
  (hj : j ≫ (groupScheme F e).X.hom = H.X.hom ≫ b)

/-- The actual affine jet chart as a relative point of the supplied ambient group. -/
def affineJetPoint (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
      (projection H n ⁻¹ᵁ U)
    (algSpec R).obj (op (CommAlgCat.of R Γ(scheme H n, projection H n ⁻¹ᵁ U))) ⟶
      (groupScheme F e).X := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
    (projection H n ⁻¹ᵁ U)
  have hb : Spec.map (CommRingCat.ofHom
      (algebraMap R Γ(scheme H n, projection H n ⁻¹ᵁ U))) =
        (isAffineOpen_jetPreimage H n U).fromSpec ≫ projection H n ≫ b := by
    exact (spec_coordinateMap (projection H n ≫ b)
      (projection H n ⁻¹ᵁ U) (isAffineOpen_jetPreimage H n U)).trans
        (Category.assoc _ _ _)
  refine Over.homMk
    ((isAffineOpen_jetPreimage H n U).fromSpec ≫ inclusion H n ≫ j) ?_
  change ((isAffineOpen_jetPreimage H n U).fromSpec ≫ inclusion H n ≫ j) ≫
    (groupScheme F e).X.hom = _
  rw [Category.assoc, Category.assoc, hj]
  exact hb.symm

/-- Its scheme map is the canonical actual jet chart followed by ambient inclusion. -/
theorem affineJetPoint_left (n : ℕ) (U : S.affineOpens) :
    (affineJetPoint H F e b j hj n U).left =
      (isAffineOpen_jetPreimage H n U).fromSpec ≫ inclusion H n ≫ j := rfl

private theorem spec_affinePointClassification {A : CommAlgCat R}
    (x : (algSpec R).obj (op A) ⟶ (groupScheme F e).X) :
    Spec.map (CommRingCat.ofHom
      (e.homEquiv.symm (affinePointsEquiv F e A x)).hom.toRingHom) = x.left := by
  rw [affinePointsEquiv_apply, Equiv.symm_apply_apply]
  exact congrArg (fun f => f.left) (algSpec.fullyFaithful.map_preimage x)

/-- The actual affine jet point is classified by its exact jet-coordinate ring map. -/
theorem affineJetPoint_coordinates (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
      (projection H n ⁻¹ᵁ U)
    (e.homEquiv.symm (affinePointsEquiv F e
        (CommAlgCat.of R Γ(scheme H n, projection H n ⁻¹ᵁ U))
        (affineJetPoint H F e b j hj n U))).hom.toRingHom =
      jetCoordinateMap H j n U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
    (projection H n ⁻¹ᵁ U)
  have hs := spec_affinePointClassification F e (affineJetPoint H F e b j hj n U)
  rw [affineJetPoint_left, ← spec_jetCoordinateMap] at hs
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)

end Langlands.GroupScheme.IdentityJet
