import Langlands.GroupScheme.Rational.SemistandardIntersection
import Langlands.GroupScheme.Dynamic.Basic

/-! # The geometric radical of a dynamic parabolic -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a connected reductive group over an arbitrary field, the actual
identity-limit subgroup is the geometric unipotent radical of the actual
dynamic parabolic. The representatives and their compatible inclusion are
arbitrary, and their representation hypotheses concern every test scheme. -/
def DynamicGeometricUnipotentRadicalStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (r : U ⟶ P),
      (Dynamic.parabolic χ).IsRepresentedBy p →
      (Dynamic.unipotent χ).IsRepresentedBy (r ≫ p) →
      IsGeometricUnipotentRadical r

end Langlands.GroupScheme
