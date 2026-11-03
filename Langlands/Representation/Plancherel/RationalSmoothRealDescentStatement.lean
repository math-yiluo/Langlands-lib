import Langlands.Representation.Plancherel.RationalImageRealPart
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic

/-!
# Smooth real homomorphisms factor through the actual valuation image

Renard V.3.19 for actual connected reductive rational points with the canonical
rational-point topology. This is a statement only.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- Every homomorphism from the rational points of a connected reductive group to the
additive reals with open kernel kills the actual common norm kernel, and factors through
the actual valuation-image projection by a unique additive real functional. -/
def RationalSmoothRealDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M),
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    ∀ f : GroupScheme.rationalPoints M →* Multiplicative ℝ,
      IsOpen (f.ker : Set (GroupScheme.rationalPoints M)) →
        rationalCommonNormKernel M ≤ f.ker ∧
          ∃! phi : rationalImageRealFunctionals M,
            ∀ g : GroupScheme.rationalPoints M,
              phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd

end Langlands.Plancherel
