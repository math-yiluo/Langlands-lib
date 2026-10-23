import Langlands.AlgebraicGeometry.ModuleLocalHomPullback

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Langlands.Scheme.Modules

/-- Pullback of local module morphisms commutes with restriction of the open. -/
def LocalHomPullbackRestrictionStatement : Prop :=
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    {U V : Y.Opens} (i : V ⟶ U) (h : LocalHom M N U),
    localHomPullback f V (LocalHom.restrict i h) =
      LocalHom.restrict ((Opens.map f.base).map i) (localHomPullback f U h)

/-- Pullback of local module morphisms is semilinear in the local scalar. -/
def LocalHomPullbackScalarStatement : Prop :=
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (U : Y.Opens) (r : Γ(Y, U)) (h : LocalHom M N U),
    localHomPullback f U (r • h) = f.app U r • localHomPullback f U h

/-- The two local laws needed to assemble the internal-Hom pushforward map. -/
def LocalHomPullbackSheafLawsStatement : Prop :=
  LocalHomPullbackRestrictionStatement.{u} ∧ LocalHomPullbackScalarStatement.{u}

end Langlands.Scheme.Modules
