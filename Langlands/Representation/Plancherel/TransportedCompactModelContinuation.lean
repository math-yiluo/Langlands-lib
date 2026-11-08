import Langlands.Representation.Plancherel.CompactInductionModelChange
import Langlands.Representation.Plancherel.UnramifiedOperatorTransport
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation

/-! # Compact-model continuation with transported character parameters -/

noncomputable section

set_option maxRecDepth 2048

open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

universe uG uH uI uV

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
  {H : Type uH} [Group H] [TopologicalSpace H]
  (e : H ≃ₜ* M)
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection) (hr' : Continuous h'.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (Ω : Set (unramifiedCharacters ν))
  (J : ∀ χ : Ω,
    (UnramifiedLeviInduction h hU
      (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e ν χ.val) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU'
        (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e ν χ.val) A).representation)
  (p : RationalOperatorContinuationData Ω
    (fun χ => compactIntertwiningOperator h hU hδ K₀ hP hK₀ hPK₀
      (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)
      (fun i => (hν i).comp e.symm.continuous) hr
      h' hU' hδ' hP' hP'K₀ hr'
      (unramifiedCharactersHomeomorph e ν χ.val) A (J χ)))

set_option quotPrecheck false in
local notation "νM" => (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν
set_option quotPrecheck false in
local notation "hνM" => (fun i => (hν i).comp e.symm.continuous)
local notation "S" => unramifiedCompactModelEquiv
  h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ νM hνM hr A
local notation "T" => unramifiedCompactModelEquiv
  h' hU' hδ' K₀ K₁ hP' hK₀ hK₁ hP'K₀ hP'K₁ νM hνM hr' A

/-- Transport a supplied whole-operator continuation of an actual ambient
intertwiner family to a second compact model. The numerator is conjugated by
the actual polynomial transitions after transporting their character parameters.
The denominator in the original parameter algebra is unchanged. -/
def transportedCompactModelContinuation :
    RationalOperatorContinuationData Ω
      (fun χ => compactIntertwiningOperator h hU hδ K₁ hP hK₁ hPK₁
      νM hνM hr h' hU' hδ' hP' hP'K₁ hr' (χM χ.val) A (J χ)) where
  denominator := p.denominator
  denominator_nonzero := p.denominator_nonzero
  numerator χ := (T (χM χ)).toLinearMap.comp
    ((p.numerator χ).comp (S (χM χ)).symm.toLinearMap)
  polynomial := by
    have hT : IsPolynomialOperatorOn (Set.univ : Set (unramifiedCharacters ν))
        (fun χ => (T (χM χ.val)).toLinearMap) := by
      exact
        (isPolynomialOperatorOn_transport_iff e ν Set.univ
          (fun χ => (T χ.val).toLinearMap)).mpr
            (unramifiedCompactModelEquiv_polynomial
              h' hU' hδ' K₀ K₁ hP' hK₀ hK₁ hP'K₀ hP'K₁ νM hνM hr' A Set.univ)
    have hS : IsPolynomialOperatorOn (Set.univ : Set (unramifiedCharacters ν))
        (fun χ => (S (χM χ.val)).symm.toLinearMap) := by
      exact
        (isPolynomialOperatorOn_transport_iff e ν Set.univ
          (fun χ => (S χ.val).symm.toLinearMap)).mpr
            (unramifiedCompactModelEquiv_symm_polynomial
              h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ νM hνM hr A Set.univ)
    exact hT.comp (p.polynomial.comp hS)
  clears χ := by
    apply LinearMap.ext
    intro f
    have hn := compactIntertwiningOperator_modelChange
      h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ νM hνM hr A
      h' hU' hδ' hP' hP'K₀ hP'K₁ hr' (χM χ.val) (J χ) ((S (χM χ.val)).symm f)
    rw [Representation.Equiv.apply_symm_apply] at hn
    change T (χM χ.val) (p.numerator χ.val ((S (χM χ.val)).symm f)) = _
    rw [p.clears χ]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (fun z => p.denominator.val χ.val • z) hn.symm

local notation "transport" => transportedCompactModelContinuation
  h hU hδ h' hU' hδ' K₀ K₁ hP hP' hK₀ hK₁
  hPK₀ hPK₁ hP'K₀ hP'K₁ e ν hν hr hr' A Ω J p

/-- No extra denominator is introduced by a change of actual compact model. -/
@[simp]
theorem transportedCompactModelContinuation_denominator :
    (transport).denominator = p.denominator := rfl

/-- The numerator is parameterwise conjugation by the actual transitions. -/
theorem transportedCompactModelContinuation_numerator (χ : unramifiedCharacters ν) :
    (transport).numerator χ =
      (T (χM χ)).toLinearMap.comp ((p.numerator χ).comp (S (χM χ)).symm.toLinearMap) := rfl

/-- The regular parameter region is exactly the original regular region. -/
@[simp]
theorem transportedCompactModelContinuation_regularRegion :
    (transport).regularRegion = p.regularRegion := rfl

/-- On the regular region the continued operators obey actual model
conjugation, with the transitions evaluated at the same parameter. -/
theorem transportedCompactModelContinuation_continuedOperator (χ : p.regularRegion) :
    (transport).continuedOperator χ =
      (T (χM χ.val)).toLinearMap.comp
        ((p.continuedOperator χ).comp (S (χM χ.val)).symm.toLinearMap) := by
  apply LinearMap.ext
  intro f
  simp only [RationalOperatorContinuationData.continuedOperator,
    transportedCompactModelContinuation, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

/-- Equivalently, the continued square commutes on the full original regular
region, with no additional naturality premise. -/
theorem transportedCompactModelContinuation_continuedOperator_natural (χ : p.regularRegion)
    (f : CompactInductionPicture h K₀ A) :
    (transport).continuedOperator χ (S (χM χ.val) f) =
      T (χM χ.val) (p.continuedOperator χ f) := by
  rw [transportedCompactModelContinuation_continuedOperator]
  change T (χM χ.val) (p.continuedOperator χ ((S (χM χ.val)).symm (S (χM χ.val) f))) = _
  rw [Representation.Equiv.symm_apply_apply]

end Langlands.Plancherel
