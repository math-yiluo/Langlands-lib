import Langlands.Geometry.Building.KPParahoric
import Langlands.GroupScheme.Rational.PointTopology

/-!
# Compact openness of the actual centralizer-zero subgroup

The local-field consequence of KP Proposition 2.2.12, Fact 2.2.3 and
Lemma 2.6.24 for the minimal Levi subgroup `Z = Z_G(S)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The supplied actual subgroup `Z(F)^0 = Z(K)^0 ∩ Z(F)` is compact and open
in the canonical topology on `Z(F)`. This is a statement target with no
additional apartment, compactness, openness or boundedness premise. -/
def CentralizerZeroCompactOpenStatement : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsAffine P.centralizer.Z.X.left := by
    have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
      P.centralizer.isClosedSubgroup
    exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
  letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
    rationalPointTopology F P.centralizer.Z.X
  IsCompact (P.centralizerZero : Set (rationalPoints P.centralizer.Z)) ∧
    IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z))

end Langlands.Geometry.Building.ParahoricBuildingData
