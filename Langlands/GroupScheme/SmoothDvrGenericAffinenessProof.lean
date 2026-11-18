import Langlands.GroupScheme.SmoothDvrGenericAffinenessDescent
import Langlands.GroupScheme.SmoothDvrLocalAffinization
import Langlands.GroupScheme.FlatPidAffinization.Group
import Langlands.AlgebraicGeometry.SmoothDvrFibreDenseAffineOpen

/-! # Smooth DVR groups with affine generic fibre are affine -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The smooth case of the DVR generic-affineness criterion, in every universe. -/
theorem smoothDvrGenericAffineness : SmoothDvrGenericAffinenessStatement.{u} := by
  apply SmoothDvrGenericAffinenessDescent.smoothDvrGenericAffineness_of_strictHenselian
  intro R _ _ _ _ _ K _ _ _ G hsm hqc hsep hη
  let := hsm
  let := hqc
  let := hsep
  have : IsAffine (pullback G.X.hom (Spec.algebraMap R K)) :=
    @isAffine_of_isAffineHom _ _
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).X.hom hη
      inferInstance
  let : GrpObj (canonicalAffinization G.X) := FlatPidAffinization.groupStructure G
  let : IsMonHom (toCanonicalAffinization G.X) :=
    FlatPidAffinization.toAffinization_isMonHom G
  let U := smoothDvrFibreDenseAffineOpen R G.X.left G.X.hom
  apply SmoothDvrLocalAffinization.isAffineHom K G U.property.1
  intro x hx
  obtain ⟨y, hy, hsame, hyx⟩ := U.property.2 x
  exact ⟨y, hy, hsame.trans hx, hyx⟩

end Langlands.GroupScheme
