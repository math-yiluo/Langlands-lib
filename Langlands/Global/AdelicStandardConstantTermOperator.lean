import Langlands.Global.AdelicStandardConstantTermIntegral
import Langlands.Analysis.FundamentalDomainConstantTermOperator

/-! # Constant terms along standard unipotent radicals as `L²` contractions

For a connected reductive `G` over a number field and `J ⊆ Δ₀`, the constant term along the
standard unipotent radical `U_J` is a continuous linear operator of norm at most one on
`L²(W · μ|_D)`, where `D` is a Borel fundamental domain of `P₀(F)` in `G(𝔸)`, `μ` is Haar
measure and `W` is any measurable weight invariant under `P₀(F)` and under `U_J(𝔸)` on the left.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage

/-- **Statement form.** For every `J ⊆ Δ₀` and every measurable weight `W` on `G(𝔸)` invariant
under `P₀(F)` and under `U_J(𝔸)` on the left, the folded constant term along `U_J` defines a
continuous linear operator of norm at most one on `L²((μ|_D).withDensity W)`, for Haar
measure `μ` and the Borel fundamental domain `D` of `P₀(F)`. It is computed on every
measurable representative. -/
def StandardConstantTermOperatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
    ∀ J ⊆ simpleRelativeRoots i ν,
      haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
      haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
        hcl.locallyCompactSpace
      ∀ (W : AdelicGroupPoints F G → ℝ≥0∞), Measurable W →
        (∀ l ∈ minimalParabolicImage F G i ν, ∀ x, W (l * x) = W x) →
        (∀ w ∈ adelicPoints F G (standardUnipotent i ν J), ∀ x, W (w * x) = W x) →
      let D := LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
        (isDiscrete_minimalParabolicImage F G i ν)
      let μW : Measure (AdelicGroupPoints F G) :=
        ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict D).withDensity W
      ∃ Tct : Lp ℂ 2 μW →L[ℂ] Lp ℂ 2 μW,
        ‖Tct‖ ≤ 1 ∧ ∀ (Fn : Lp ℂ 2 μW) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
          f =ᵐ[μW] Fn →
          Tct Fn =ᵐ[μW] foldConstantTerm (minimalParabolicImage F G i ν) D
              (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G i ν))
              (adelicPoints F G (standardUnipotent i ν J)).subtype Measure.haar
              (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent i ν J)) f

/-- Proof of `StandardConstantTermOperatorStatement`. -/
theorem standardConstantTermOperator : StandardConstantTermOperatorStatement.{u} := by
  intro F _ _ G _ _ _ T i ν hG hi hν J hJ
  have hcl : IsClosed (adelicPoints F G (standardUnipotent i ν J) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_standardUnipotent F G i ν J
  have : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) := hcl.locallyCompactSpace
  have : CompactSpace (RationalQuotient F G (standardUnipotent i ν J)) :=
    compactSpace_standardUnipotent F G i ν hG hi hν J hJ
  intro W hW hWΛ hWV D μW
  let U := standardUnipotent i ν J
  let Λ := minimalParabolicImage F G i ν
  have hΛ := isDiscrete_minimalParabolicImage F G i ν
  have : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  have hΓ := And.intro
    (rationalSubgroup_standardUnipotent_le F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
    (conj_rationalSubgroup_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
  have hnorm := conj_adelicPoints_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
  have : (Measure.haar : Measure (adelicPoints F G U)).IsMulRightInvariant :=
    haar_isMulRightInvariant_of_compactRationalQuotient F G U
  have : (Measure.haar : Measure (adelicPoints F G U)).IsInvInvariant :=
    ConstantTermAverage.isInvInvariant_of_isMulRightInvariant _
  have hCm : MeasurableSet (ConstantTermAverage.rationalFundamentalDomain F G U) :=
    LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_rationalSubgroup F G U)
  have hC : IsFundamentalDomain (rationalSubgroup F G U)
      (ConstantTermAverage.rationalFundamentalDomain F G U) Measure.haar :=
    LeftCosetSpace.isFundamentalDomain _ (isDiscrete_rationalSubgroup F G U) _
  exact foldConstantTermOperator (Measure.haar : Measure (AdelicGroupPoints F G)) Λ
    (LeftCosetSpace.fundamentalDomain Λ hΛ) (LeftCosetSpace.measurableSet_fundamentalDomain Λ hΛ)
    (LeftCosetSpace.fundamentalDomain_unique Λ hΛ) (adelicPoints F G U).subtype
    continuous_subtype_val.measurable Subtype.val_injective (rationalSubgroup F G U)
    (fun w hw => hΓ.1 w hw) (fun l => ConstantTermAverage.conjEquiv F G U Λ hnorm l)
    (fun _ _ => rfl)
    (fun l w hw => (ConstantTermAverage.mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l w).mp hw)
    Measure.haar (ConstantTermAverage.measurePreserving_conjEquiv F G U Λ hΓ hnorm)
    (ConstantTermAverage.rationalFundamentalDomain F G U) hCm hC
    (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_zero U)
    (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_top U) W hW
    (fun l x => hWΛ l l.2 x) (fun w x => hWV w w.2 x)

end Langlands.Global.StandardConstantTerm
