import Langlands.GroupScheme.Reductive.Basic
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.CategoryTheory.RenardFiniteType

/-! # The category of smooth representations is Noetherian

Renard 2026, VI.7.5, Proposition (printed p.186 / PDF p.192): the category `M(G)` of smooth
representations is Noetherian in the sense of Appendix A.I.3: every object of finite type is a
Noetherian object.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.7.5, Proposition, for all actual connected reductive groups: the category of
smooth complex representations of `G(F)` (carriers in universe `v`) is Noetherian in Renard's
sense (Appendix A.I.3): arbitrary subobject unions exist and every object of finite type is a
Noetherian object. -/
def SmoothRepNoetherianCategoryStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)],
      Langlands.Renard.IsNoetherianCategory (SmoothRep.{0, u, v} ℂ (rationalPoints G))

end Langlands.Aubert.General.RepresentedParabolic
