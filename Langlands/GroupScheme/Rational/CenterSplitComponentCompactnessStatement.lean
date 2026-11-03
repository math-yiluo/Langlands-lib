import Langlands.GroupScheme.Rational.CenterSplitComponent
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Compactness of the actual scheme-center point quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Compactness of the full scheme-center point quotient by an actual split component,
with the canonical inherited topology and its quotient topology. -/
def CenterSplitComponentCompactness
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M)
    (A : CommGroupScheme (Spec (CommRingCat.of F))) (i : A.toGrp ⟶ M)
    (hi : IsSplitComponent i) : Prop :=
  letI : IsAffineHom M.X.hom := hM.isAffineHom
  letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  letI : TopologicalSpace
      (CentralPointQuotient i hi.isCentralSplitTorus.isCentral) :=
    centralPointQuotientTopology i hi.isCentralSplitTorus.isCentral
  CompactSpace (CentralPointQuotient i hi.isCentralSplitTorus.isCentral)

/-- WST-CEN-01 for every actual connected reductive group and every actual split component
over every nonarchimedean local field, in either characteristic. -/
def CenterSplitComponentCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M)
    (A : CommGroupScheme (Spec (CommRingCat.of F))) (i : A.toGrp ⟶ M)
    (hi : IsSplitComponent i),
    CenterSplitComponentCompactness M hM A i hi

end Langlands.GroupScheme
