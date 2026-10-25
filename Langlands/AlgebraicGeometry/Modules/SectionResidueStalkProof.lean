import Langlands.AlgebraicGeometry.Modules.UnitEndResidueStalkProof
import Langlands.AlgebraicGeometry.Modules.SectionResidueStatements
import Langlands.AlgebraicGeometry.Modules.ResidueLocalChartProof

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

open Langlands.AlgebraicGeometry.Picard

/-- A line-bundle section has nonzero actual residue value exactly when it is a stalk frame. -/
theorem lineBundleResidueStalkCriterion : LineBundleResidueStalkCriterion.{u} := by
  intro X L s x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.property x
  let y : U.toScheme := ⟨x, hxU⟩
  let φ := sectionHom L.obj s
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e.hom
  have hψ : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ.mapPresheaf) ↔
      IsStalkFrame L.obj s x := by
    change IsIso (((Scheme.Modules.toPresheaf U.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ) ↔ _
    simp only [ψ, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
    exact isIso_stalk_restrict_iff φ U y
  exact (residueLocalChartCriterion X L.obj s U y e).trans
    ((unitEnd_stalkIso_iff_residue_ne_zero ψ y).symm.trans hψ)

end Langlands.SchemeModule
