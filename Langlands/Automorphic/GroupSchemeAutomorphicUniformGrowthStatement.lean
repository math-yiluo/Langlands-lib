import Langlands.Automorphic.GroupSchemeActualDifferential
import Langlands.Automorphic.GroupSchemeForms

/-! # Every actual adelic automorphic form has uniformly moderate growth -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- For a connected reductive group, a maximal compact subgroup `Kinf` of the infinite adelic
points and a closed matrix representation, every original finite plot-smooth rational function
satisfying the published form conditions (`Kinf`-finite, centre-finite, of moderate growth) has
uniformly moderate growth: one real exponent bounds every actual enveloping derivative. -/
def AdelicAutomorphicUniformGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N d : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    GroupScheme.IsConnectedReductive G → GroupScheme.IsClosedSubgroup rho →
    CompactIwasawa.IsMaximalCompact Kinf → 0 < N →
    ∀ f : FinitePlotSmoothRationalFunctions F G,
      IsAdelicAutomorphicForm F G Kinf rho hsmooth
          (adelicDifferentialCommutator_of_smooth F G hsmooth) f →
        HasAdelicUniformModerateGrowth F G rho hsmooth
          (adelicDifferentialCommutator_of_smooth F G hsmooth) f

end Langlands.Automorphic.GroupSchemeFunctions
