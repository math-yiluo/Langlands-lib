import Langlands.Representation.Plancherel.RationalImaginaryParameters

/-! # Actual periods and the compact imaginary parameter quotient -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- The original period subgroup is discrete and closed, and the actual
imaginary exponential identifies its compact quotient with unitary characters. -/
def RationalImaginaryParameterQuotientStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    letI := rationalImageComplexParameterTopology G
    DiscreteTopology (rationalImagePeriodLattice G) ∧
      IsClosed (rationalImagePeriodLattice G : Set (rationalImageComplexFunctionals G)) ∧
      DiscreteTopology (rationalImageImaginaryPeriodLattice G) ∧
      IsClosed (rationalImageImaginaryPeriodLattice G :
        Set (rationalImageImaginaryParameters G)) ∧
      CompactSpace (rationalImageImaginaryParameters G ⧸
        rationalImageImaginaryPeriodLattice G) ∧
      IsOpenQuotientMap (rationalImageImaginaryCharacter G) ∧
      (∃ e : (rationalImageImaginaryParameters G ⧸
          rationalImageImaginaryPeriodLattice G) ≃ₜ
            unitaryCharacters (rationalDiscreteValuationImage G),
        ∀ lam : rationalImageImaginaryParameters G,
          e (QuotientAddGroup.mk lam) = rationalImageImaginaryCharacter G lam) ∧
      IsOpenQuotientMap (rationalCanonicalImaginaryUnramifiedCharacter G) ∧
      (∃ e : (rationalImageImaginaryParameters G ⧸
          rationalImageImaginaryPeriodLattice G) ≃ₜ
            unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul),
        ∀ lam : rationalImageImaginaryParameters G,
          e (QuotientAddGroup.mk lam) = rationalCanonicalImaginaryUnramifiedCharacter G lam)

end Langlands.Plancherel
