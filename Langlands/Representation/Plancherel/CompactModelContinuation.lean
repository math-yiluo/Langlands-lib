import Langlands.Representation.Plancherel.CompactInductionModelChange
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation

/-! # Transport of continuation between actual compact models -/

noncomputable section

set_option maxRecDepth 2048

open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U P' U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU')
  (K₀ K₁ : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
  (hK₀ : IsCompact (K₀ : Set G)) (hK₁ : IsCompact (K₁ : Set G))
  (hPK₀ : ∀ g : G, ∃ p : P, ∃ k : K₀, g = (p : G) * (k : G))
  (hPK₁ : ∀ g : G, ∃ p : P, ∃ k : K₁, g = (p : G) * (k : G))
  (hP'K₀ : ∀ g : G, ∃ p : P', ∃ k : K₀, g = (p : G) * (k : G))
  (hP'K₁ : ∀ g : G, ∃ p : P', ∃ k : K₁, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection) (hr' : Continuous h'.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (Ω : Set (unramifiedCharacters ν))
  (J : ∀ χ : Ω,
    (UnramifiedLeviInduction h hU ν χ.val A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ.val A).representation)
  (p : RationalOperatorContinuationData Ω
    (compactIntertwiningOperatorFamily h hU hδ h' hU' hδ'
      K₀ hK₀ hP hP' hPK₀ hP'K₀ hr hr' ν hν A Ω J))

local notation "S" => unramifiedCompactModelEquiv
  h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A
local notation "T" => unramifiedCompactModelEquiv
  h' hU' hδ' K₀ K₁ hP' hK₀ hK₁ hP'K₀ hP'K₁ ν hν hr' A

/-- Transport a supplied whole-operator continuation of an actual ambient
intertwiner family to a second compact model. The numerator is conjugated by
the actual polynomial transitions, and the denominator is unchanged. -/
def compactModelContinuation :
    RationalOperatorContinuationData Ω
      (compactIntertwiningOperatorFamily h hU hδ h' hU' hδ'
        K₁ hK₁ hP hP' hPK₁ hP'K₁ hr hr' ν hν A Ω J) where
  denominator := p.denominator
  denominator_nonzero := p.denominator_nonzero
  numerator χ := (T χ).toLinearMap.comp
    ((p.numerator χ).comp (S χ).symm.toLinearMap)
  polynomial :=
    (unramifiedCompactModelEquiv_polynomial
      h' hU' hδ' K₀ K₁ hP' hK₀ hK₁ hP'K₀ hP'K₁ ν hν hr' A Set.univ).comp
      (p.polynomial.comp (unramifiedCompactModelEquiv_symm_polynomial
        h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A Set.univ))
  clears χ := by
    apply LinearMap.ext
    intro f
    have hn := compactIntertwiningOperator_modelChange
      h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A
      h' hU' hδ' hP' hP'K₀ hP'K₁ hr' χ.val (J χ) ((S χ.val).symm f)
    rw [Representation.Equiv.apply_symm_apply] at hn
    change T χ.val (p.numerator χ.val ((S χ.val).symm f)) = _
    rw [p.clears χ]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (fun z => p.denominator.val χ.val • z) hn.symm

local notation "transport" => compactModelContinuation
  h hU hδ h' hU' hδ' K₀ K₁ hP hP' hK₀ hK₁
  hPK₀ hPK₁ hP'K₀ hP'K₁ ν hν hr hr' A Ω J p

/-- No extra denominator is introduced by a change of actual compact model. -/
@[simp]
theorem compactModelContinuation_denominator :
    (transport).denominator = p.denominator := rfl

/-- The numerator is parameterwise conjugation by the actual transitions. -/
theorem compactModelContinuation_numerator (χ : unramifiedCharacters ν) :
    (transport).numerator χ =
      (T χ).toLinearMap.comp ((p.numerator χ).comp (S χ).symm.toLinearMap) := rfl

/-- The regular parameter region is exactly the original regular region. -/
@[simp]
theorem compactModelContinuation_regularRegion :
    (transport).regularRegion = p.regularRegion := rfl

/-- On the regular region the continued operators obey actual model
conjugation, with the transitions evaluated at the same parameter. -/
theorem compactModelContinuation_continuedOperator (χ : p.regularRegion) :
    (transport).continuedOperator χ =
      (T χ.val).toLinearMap.comp
        ((p.continuedOperator χ).comp (S χ.val).symm.toLinearMap) := by
  apply LinearMap.ext
  intro f
  simp only [RationalOperatorContinuationData.continuedOperator,
    compactModelContinuation, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

/-- Equivalently, the continued square commutes on the full original regular
region, with no additional naturality premise. -/
theorem compactModelContinuation_continuedOperator_natural (χ : p.regularRegion)
    (f : CompactInductionPicture h K₀ A) :
    (transport).continuedOperator χ (S χ.val f) =
      T χ.val (p.continuedOperator χ f) := by
  rw [compactModelContinuation_continuedOperator]
  change T χ.val (p.continuedOperator χ ((S χ.val).symm (S χ.val f))) = _
  rw [Representation.Equiv.symm_apply_apply]

end Langlands.Plancherel
