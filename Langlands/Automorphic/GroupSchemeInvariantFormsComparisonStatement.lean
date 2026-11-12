import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Comparison of automorphic functions on `G(F) \ G(𝔸)` with the existing forms

For the subgroup of rational points, the automorphic functions of
`GroupSchemeInvariantForms` are exactly the evaluations of the existing
`IsAdelicAutomorphicForm` elements of the finite plot-smooth carrier. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- For every affine group scheme `G` over a number field, smooth of relative
dimension `d` with the existing atlas and commutator premise, every subgroup
`Kinf` of the infinite adelic points and every matrix representation `rho`, a
function `φ` on `G(𝔸)` satisfies `IsAutomorphicFunctionOn` for the subgroup of
rational points if and only if it is the evaluation of an element `f` of the
existing finite plot-smooth carrier with `IsAdelicAutomorphicForm f`. -/
def RationalAutomorphicFunctionComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N d : ℕ}
    (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
    IsAutomorphicFunctionOn F G hsmooth hcalc (AdelicGroupPoints.rationalSubgroup F G) Kinf rho φ ↔
      ∃ f : FinitePlotSmoothRationalFunctions F G,
        evaluate F G f.val = φ ∧ IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f

end Langlands.Automorphic.GroupSchemeFunctions
