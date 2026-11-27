import Langlands.GroupScheme.Rational.NumberFieldQuadraticQuasiSplitToralReduction
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelExistence
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelRealControl
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelRigidTorus

/-! # Anisotropic toral reduction for quadratic cocycles -/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- An opposite-Borel torus gives real-controlled representatives on the
original quadratic cover. Rigidity of the Cartan matrix makes the torus split
over the covering field and anisotropic over the base. -/
theorem numberFieldQuadraticQuasiSplitToralReduction :
    NumberFieldQuadraticQuasiSplitToralReductionStatement.{u} := by
  intro F _ _ G _ _ d hrigid L _ _ _ _ hL hqs ξ hξ
  let hG := d.isSemisimple.isConnectedReductive
  obtain ⟨T, i, hi⟩ := exists_quadraticOppositeBorelTorus hL hG hqs
  obtain ⟨hsplit, hanisotropic⟩ := hi.split_anisotropic d hrigid
  obtain ⟨η, hcoh, hη⟩ := hi.exists_realLocallyTrivialRepresentative hG ξ hξ
  exact ⟨T, i, η, hi.2.1, hsplit, hanisotropic, hη, hcoh.symm⟩

end Langlands.GroupScheme
