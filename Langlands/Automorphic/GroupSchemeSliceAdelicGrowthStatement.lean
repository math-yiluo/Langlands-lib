import Langlands.Automorphic.GroupSchemeGrowth
import Langlands.Automorphic.GroupSchemeAdelicGrowth
import Langlands.Automorphic.GroupSchemeFiniteLevel
import Langlands.GroupScheme.Reductive.Basic

/-! # Slice-wise polynomial growth at finite level gives full adelic moderate growth -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- For a connected reductive group and a closed matrix representation, every continuous
rational-invariant function with an open finite-adelic stabilizer whose infinite slices all
have polynomial growth (with constants and exponents that may depend on the slice) has one
moderate-growth bound on all adelic points. -/
def AdelicSliceModerateGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {N : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N)),
    GroupScheme.IsConnectedReductive G → GroupScheme.IsClosedSubgroup rho → 0 < N →
    ∀ f : ContinuousRationalFunctions F G,
      f ∈ (finiteSmoothSubrepresentation F G).toSubmodule →
      Langlands.Automorphic.GroupSchemeFunctions.HasPolynomialGrowth F G rho f →
        HasAdelicModerateGrowth F G rho f

end Langlands.Automorphic.GroupSchemeFunctions
