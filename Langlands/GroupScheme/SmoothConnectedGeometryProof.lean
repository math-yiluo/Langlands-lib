import Langlands.GroupScheme.SmoothConnectedGeometryStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent

/-! # Geometric integrality of smooth connected affine group schemes -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency.types false in
private theorem geometricallyConnected_of_connected_affine
    (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] :
    GeometricallyConnected H.X.hom := by
  let : GrpObj (Over.mk H.X.hom) := H.grp
  obtain ⟨G₀, i, L₀, hi, -, -, -, hgc, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k (GoodReductionJacobian.relativeGroupLawOfGrpObj k H.X.hom)
  let : IsOpenImmersion i := hi
  have hr : Set.range i = Set.univ := by
    rw [hrange, PreconnectedSpace.connectedComponent_eq_univ]
  have : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i (by
    ext x
    change x ∈ Set.range i ↔ x ∈ (Set.univ : Set H.X.left)
    rw [hr])
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected) i H.X.hom).mp hgc

set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth connected affine groups and their actual products have the required geometry. -/
theorem smoothConnectedAffineGeometry : SmoothConnectedAffineGeometryStatement.{u} := by
  have groupIntegral : SmoothConnectedAffineGroupIntegralStatement.{u} := by
    intro k _ H hsm haff hconn
    let : Smooth H.X.hom := hsm
    let : IsAffineHom H.X.hom := haff
    let : ConnectedSpace H.X.left := hconn
    exact Langlands.AbelianScheme.smoothGeometricIntegrality k H.X.left H.X.hom hsm
      (geometricallyConnected_of_connected_affine k H)
  refine ⟨groupIntegral, ?_⟩
  intro k _ H₁ H₂ hsm₁ haff₁ hconn₁ hsm₂ haff₂ hconn₂
  let : Smooth H₁.X.hom := hsm₁
  let : IsAffineHom H₁.X.hom := haff₁
  let : ConnectedSpace H₁.X.left := hconn₁
  let : Smooth H₂.X.hom := hsm₂
  let : IsAffineHom H₂.X.hom := haff₂
  let : ConnectedSpace H₂.X.left := hconn₂
  let : GeometricallyConnected H₁.X.hom := geometricallyConnected_of_connected_affine k H₁
  let : GeometricallyConnected H₂.X.hom := geometricallyConnected_of_connected_affine k H₂
  have hprodSmooth : Smooth (H₁.X ⊗ H₂.X).hom := by
    change Smooth (pullback.fst H₁.X.hom H₂.X.hom ≫ H₁.X.hom)
    infer_instance
  have hprodConnected : GeometricallyConnected (H₁.X ⊗ H₂.X).hom :=
    GeometricallyConnected.comp (pullback.fst H₁.X.hom H₂.X.hom) H₁.X.hom
  refine ⟨?_, ?_, ?_, Langlands.AbelianScheme.smoothGeometricIntegrality k
    (H₁.X ⊗ H₂.X).left (H₁.X ⊗ H₂.X).hom hprodSmooth hprodConnected⟩
  · change IsAffineHom (pullback.fst H₁.X.hom H₂.X.hom ≫ H₁.X.hom)
    let : IsAffineHom (pullback.fst H₁.X.hom H₂.X.hom) :=
      MorphismProperty.pullback_fst _ _ haff₂
    infer_instance
  · let := hprodSmooth
    infer_instance
  · change QuasiCompact (pullback.fst H₁.X.hom H₂.X.hom ≫ H₁.X.hom)
    infer_instance

end Langlands.GroupScheme
