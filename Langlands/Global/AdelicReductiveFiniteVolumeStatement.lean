import Langlands.Global.AdelicFiniteVolumeStatement
import Langlands.GroupScheme.Reductive.Basic

/-! # Finite volume of the norm-one adelic rational quotient of a connected reductive group -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-- The finite-volume assertion of Getz–Hahn, Theorem 2.6.3, for connected reductive groups
over number fields (Borel–Harish-Chandra), for the existing quotient of actual norm-one Haar by
actual principal counting. This proposition is a target and supplies no proof or measure
instance. -/
def ConnectedReductiveFiniteVolumeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G)

/-- The connected reductive case is a special case of the general finite-volume assertion. -/
theorem connectedReductiveFiniteVolumeStatement_of_normOne
    (h : NormOneRationalQuotientFiniteVolumeStatement.{u}) :
    ConnectedReductiveFiniteVolumeStatement.{u} :=
  fun F _ _ G _ _ hG => h F G hG.smooth hG.connectedSpace

end Langlands.Global.AdelicGroupPoints
