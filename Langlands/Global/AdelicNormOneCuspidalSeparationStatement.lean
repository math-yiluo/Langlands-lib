import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Separation of continuous cuspidal functions by norm-one tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section NormOne

variable {F : Type u} [Field F] [NumberField F]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The pointwise cuspidality condition along the proper rational
parabolics of an actual reductive group. -/
def HasZeroProperParabolicConstantTerms (f : AdelicGroupPoints F H → ℂ) : Prop :=
  ∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ H) (r : U ⟶ P)
    [IsAffine U.X.left] [IsClosedImmersion (r ≫ p).hom.hom.left],
    IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
      SubgroupFunctor.range p ≠ ⊤ → subgroupConstantTerm F (r ≫ p) f = 0

/-- The function used to pair a right translate with an automorphic cusp test
on the norm-one rational quotient. -/
def normOneCuspidalPairingIntegrand (f ψ : AdelicGroupPoints F H → ℂ)
    (a : AdelicGroupPoints F H) (x : NormOneRationalQuotient F H) : ℂ :=
  let m : AdelicGroupPoints F H := (Quotient.out x : normOneSubgroup F H).val
  f (m * a) * starRingEnd ℂ (ψ m)

end NormOne

/-- The cuspidal case of Mœglin–Waldspurger I.3.4, in the continuous
number-field setting and with the fibrewise norm-one tests. -/
def NormOneCuspidalSeparationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom], IsConnectedReductive H →
    ∀ {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d H.X.hom)
      (Kinf : Subgroup (InfiniteAdelicGroupPoints F H))
      (rho : MatrixRepresentation H (Fin N)),
      IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F H)) → 0 < N → IsClosedSubgroup rho →
    ∀ (f : AdelicGroupPoints F H → ℂ),
      IsLeftInvariantUnder F H (rationalSubgroup F H) f → Continuous f →
      HasModerateGrowthFunction F H rho f → HasZeroProperParabolicConstantTerms f →
      (∀ (ψ : AdelicGroupPoints F H → ℂ),
        IsAutomorphicFunctionOn F H hsmooth (adelicDifferentialCommutator_of_smooth F H hsmooth)
          (rationalSubgroup F H) Kinf rho ψ → HasZeroProperParabolicConstantTerms ψ →
        ∀ a : AdelicGroupPoints F H,
          Integrable (normOneCuspidalPairingIntegrand f ψ a) (normOneRationalQuotientHaarMeasure F H) ∧
            (∫ x, normOneCuspidalPairingIntegrand f ψ a x ∂normOneRationalQuotientHaarMeasure F H) = 0) →
      f 1 = 0

end Langlands.Global
