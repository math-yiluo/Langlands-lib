import Langlands.AlgebraicGeometry.Modules.SectionResidue
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Residue-field nonvanishing in a local rank-one chart -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

/-- In a rank-one chart, the actual residue-field section is nonzero exactly
when the local scalar representing the section has nonzero residue. -/
def ResidueLocalChartCriterion : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules) (s : GlobalSections M)
    (U : X.Opens) (x : U.toScheme) (e : M.restrict U.ι ≅ structureModule U.toScheme),
    let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s) ≫ e.hom
    NonvanishingAt M s (U.ι x) ↔
      U.toScheme.Γevaluation x (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) ≠ 0

end Langlands.SchemeModule
