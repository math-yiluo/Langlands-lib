import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyMap
import Langlands.AlgebraicGeometry.Modules.CohomologyPullback
import Langlands.Cohomology.AbelianSheafCohomologyPullback

/-! # Relative module cohomology and arbitrary sheaf-cohomology pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open DerivedSections PushforwardInjectiveAcyclic
  Langlands.Cohomology.AbelianSheafCohomologyPullback

/-- The actual additive module/sheaf comparison intertwines arbitrary-morphism
pullback with coefficients, using the specified module and sheaf adjunctions. -/
def RelativeAbelianSheafCohomologyPullbackStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X X' : Over (Spec R)) (f : X' ⟶ X)
    (M : X.left.Modules) (N : X'.left.Modules)
    (k : M ⟶ (Scheme.Modules.pushforward f.left).obj N) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj M) n),
    relativeHAddEquiv X'.hom N n
        (pushforwardMap f.left.base ((toAbSheaf X.left).map k) n x) =
      ((relativeCohomology X'.hom n).map
          (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k)).hom
        ((relativeCohomologyPullback f M n).hom (relativeHAddEquiv X.hom M n x))

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
