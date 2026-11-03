import Langlands.Global.AdelicGroupHaarMeasure
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite volume of the actual norm-one adelic rational quotient -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory

namespace Langlands.Global.AdelicGroupPoints

/-- The finite-volume assertion of Getz–Hahn, Theorem 2.6.3, over number fields,
for the existing quotient of actual norm-one Haar by actual principal counting.
This proposition is a target and supplies no proof or measure instance. -/
def NormOneRationalQuotientFiniteVolumeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    Smooth G.X.hom → ConnectedSpace G.X.left →
      IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G)

end Langlands.Global.AdelicGroupPoints
