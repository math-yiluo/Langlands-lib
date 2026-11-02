import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Local finite presentation of actual line bundles -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {X Y : Scheme.{u}}

/-- Finite local presentations constructed from the actual rank-one
trivializations, using one generator and no relations on each chosen open. -/
def IsLocallyFreeRankOne.finitePresentationData {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) :
    { p : M.QuasicoherentData // p.IsFinitePresentation } := by
  classical
  choose U hx e using hM
  let q : M.LocalGeneratorsData := {
    I := X
    X := U
    coversTop := by
      apply (_root_.Opens.coversTop_iff X U).mpr
      apply top_le_iff.mp
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
    generators x :=
      (SheafOfModules.free.generatingSections PUnit.{u + 1}).ofEpi
        (Langlands.Scheme.Modules.unitLocalBasis (e x).some).hom }
  have : q.IsLocallyFreeData := {
    isIso x := by
      change IsIso ((SheafOfModules.free.generatingSections PUnit.{u + 1}).ofEpi
        (Langlands.Scheme.Modules.unitLocalBasis (e x).some).hom).π
      rw [SheafOfModules.GeneratingSections.ofEpi_π,
        SheafOfModules.free.generatingSections_π]
      infer_instance }
  let p := q.quasiCoherentData
  have hp : p.IsFinitePresentation := {
    isFinite_presentation x := {
      isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift.{u} Empty))⟩ } }
  exact ⟨p, hp⟩

/-- An actual locally free rank-one sheaf has finite free presentations locally. -/
lemma IsLocallyFreeRankOne.isFinitePresentation {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) : M.IsFinitePresentation :=
  { exists_quasicoherentData :=
      ⟨hM.finitePresentationData.val, hM.finitePresentationData.property⟩ }

/-- The underlying sheaf of an actual line bundle is locally finitely presented. -/
instance LineBundle.isFinitePresentation (L : LineBundle X) : L.obj.IsFinitePresentation :=
  L.property.isFinitePresentation

/-- Ordinary scheme-module pullback of a locally free rank-one sheaf is locally
finitely presented. -/
lemma IsLocallyFreeRankOne.isFinitePresentation_pullback {M : Y.Modules}
    (hM : IsLocallyFreeRankOne M) (f : X ⟶ Y) :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
  (hM.pullback f).isFinitePresentation

end Langlands.AlgebraicGeometry.Picard
