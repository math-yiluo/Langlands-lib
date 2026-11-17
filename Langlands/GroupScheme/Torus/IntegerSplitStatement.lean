import Langlands.GroupScheme.Torus.Relative

/-! # Statement: every torus over the integers is split -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every étale form of a finite split torus over the lifted integers is split
(Conrad, *Reductive group schemes* (2014), Corollary B.3.6, p.293). -/
def IntegerTorusSplitStatement : Prop :=
  ∀ T : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ))),
    RelativeTorus.IsTorus T → IsSplitTorus T

end Langlands.GroupScheme
