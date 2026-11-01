import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.Modules.DerivedRestriction
import Langlands.AlgebraicGeometry.LocallyFreeRank

/-! # The canonical direct-image theorem needed for linear rigidification -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections
  Langlands.Scheme.Modules

variable {P : Prerequisites.{u}} {S S' : Scheme.{u}} {g d n : ℕ}

/-- The actual direct-image base-change map, transported through the canonical
comparison of the cubic line bundles. -/
def Datum.rigidificationBaseChangeMap (a : Datum P S g d n) (b : S' ⟶ S) :
    (Scheme.Modules.pullback b).obj a.rigidificationModule ⟶
      (a.pullback b).rigidificationModule :=
  pushforwardBaseChange b a.abelian.X.hom (a.pullback b).abelian.X.hom
      (pullback.fst a.abelian.X.hom b) pullback.condition a.cubicBundle.obj ≫
    (Scheme.Modules.pushforward (a.pullback b).abelian.X.hom).map
      (((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso b)).inv)

/-- The finite-rank and canonical arbitrary-base-change assertion for the
direct image of the actual cubic diagonal bundle. This is a theorem target. -/
def CubicDirectImageStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (g d n : ℕ), 0 < d → ∀ a : Datum P S g d n,
      IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d) ∧
        ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
          IsIso (a.rigidificationBaseChangeMap b)

end Langlands.AbelianScheme.PolarizedFiniteLevel
