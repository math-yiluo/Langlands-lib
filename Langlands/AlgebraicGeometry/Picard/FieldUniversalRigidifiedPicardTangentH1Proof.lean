import Langlands.AlgebraicGeometry.Picard.UniversalRigidifiedTangentScaling
import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationScaling
import Langlands.AlgebraicGeometry.Picard.FieldUniversalRigidifiedPicardTangentH1Statement

/-! # Actual tangent-to-H1 comparison for a universal rigidified Picard parameter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
open Langlands.AlgebraicGeometry.Picard.DualNumberThickening
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

/-- The actual sheaf tangent at the trivial parameter is linearly equivalent to actual
right-derived structure-sheaf H1 over every field. -/
theorem fieldUniversalRigidifiedPicardTangentH1 :
    FieldUniversalRigidifiedPicardTangentH1Statement.{u} := by
  intro k _ A P U hU _hP
  let preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    @pullbackTensorComparisonIsIso.{u}
  let 𝒰 := CechResolution.orderedAffineCoverOfQuasiCompact A.X.hom
  let E := (tangentDeformationAddEquiv preservation A.X.hom (unitSection A)
    (unitSection_comp A) U hU).trans (deformationH1AddEquiv preservation A.X.hom 𝒰)
  refine ⟨{ E with map_smul' := ?_ }⟩
  intro c t
  change deformationH1AddEquiv preservation A.X.hom 𝒰
      (Additive.ofMul (tangentDeformationEquiv preservation A.X.hom (unitSection A)
        (unitSection_comp A) U hU (c • t))) =
    c • deformationH1AddEquiv preservation A.X.hom 𝒰
      (Additive.ofMul (tangentDeformationEquiv preservation A.X.hom (unitSection A)
        (unitSection_comp A) U hU t))
  have hs : tangentDeformationEquiv preservation A.X.hom (unitSection A)
      (unitSection_comp A) U hU (c • t) =
    scaleClass A.X.hom preservation c
      (tangentDeformationEquiv preservation A.X.hom (unitSection A)
        (unitSection_comp A) U hU t) := by
    apply Subtype.ext
    exact tangentDeformationEquiv_smul_val preservation A.X.hom (unitSection A)
      (unitSection_comp A) U hU c t
  rw [hs, deformationH1AddEquiv_scaleClass]

end Langlands.AbelianScheme
