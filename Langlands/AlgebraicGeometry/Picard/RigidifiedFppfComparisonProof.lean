import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedComparisonOfSheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesAffineSheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSheafGeneral
import Langlands.AlgebraicGeometry.Picard.RigidifiedRelativeIsoUniqueness
import Langlands.AlgebraicGeometry.Sites.OverFppfSheaf
import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof

/-! # Proof of the canonical rigidified comparison with the fppf Picard sheaf -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Under the universal structure-sheaf condition and a section, the canonical
forget-rigidification map from rigidified classes to the fppf Picard sheaf is an
isomorphism. -/
theorem rigidifiedFppfComparison : RigidifiedFppfComparisonStatement.{u} := by
  intro S X f _ _ ε section_eq hO
  have unique := RigidifiedLineBundle.relative_iso_subsingleton f ε section_eq hO
  exact RigidifiedLineBundle.toPicardSheaf_isIso_of_isSheaf f ε section_eq
    (OverFppfSheaf.isSheaf_fppfTopology_over _
      (RigidifiedLineBundle.classPresheaf_isSheaf_zariski_of_unique f ε section_eq unique)
      (fun φ hf hs s ↦ RigidifiedLineBundle.classPresheaf_isSheafFor_affine f ε section_eq
        Langlands.Scheme.Modules.LineBundleIsoDescent.lineBundleIsoDescent
        Langlands.Scheme.Modules.lineBundleDescentEffective unique φ hf hs s))

end Langlands.AlgebraicGeometry.Picard
