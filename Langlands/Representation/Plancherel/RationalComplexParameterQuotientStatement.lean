import Langlands.Representation.Plancherel.RationalParameterTopology
import Mathlib.Topology.Algebra.Group.Quotient

/-! # The topological quotient of the actual complex parameter space -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- The actual complex exponential is an open quotient map and identifies the
quotient by its stated period subgroup with the actual character spaces. -/
def RationalComplexParameterQuotientStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    letI := rationalImageComplexParameterTopology G
    IsOpenQuotientMap (rationalImageComplexCharacter G) ∧
      (∃ e : (rationalImageComplexFunctionals G ⧸ rationalImagePeriodLattice G) ≃ₜ
          rationalImageCharacters G,
        ∀ lam : rationalImageComplexFunctionals G,
          e (QuotientAddGroup.mk lam) = rationalImageComplexCharacter G lam) ∧
      IsOpenQuotientMap (fun lam : rationalImageComplexFunctionals G =>
        rationalCanonicalUnramifiedComplexExponential G (Multiplicative.ofAdd lam)) ∧
      (∃ e : (rationalImageComplexFunctionals G ⧸ rationalImagePeriodLattice G) ≃ₜ
          unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul),
        ∀ lam : rationalImageComplexFunctionals G,
          e (QuotientAddGroup.mk lam) =
            rationalCanonicalUnramifiedComplexExponential G (Multiplicative.ofAdd lam))

end Langlands.Plancherel
