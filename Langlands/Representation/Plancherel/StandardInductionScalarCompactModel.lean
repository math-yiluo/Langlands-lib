import Langlands.Representation.Plancherel.StandardInductionScalarCompactModelStatement
import Langlands.Representation.Plancherel.TransportedCompactModelContinuation

/-! # Compact-model independence of actual canonical standard scalars -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV

/-- The canonical fraction of the actual standard-integral composite is
unchanged by the compact subgroup used to realize normalized induction. -/
theorem conditionalStandardInductionScalarCompactModel :
    ConditionalStandardInductionScalarCompactModelStatement.{u, uG, uV} := by
  intro F _ _ _ _ L _ hp hL G _ _ _ _ _ P₀ P₁ M U₀ U₁
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₀ K₁ hK₀ hK₁ hP₀ hP₁
    hP₀K₀ hP₁K₀ hP₀K₁ hP₁K₁ hr₀ hr₁ e hν A
    _ _ _ _ _ _ _ _ _ _ _ _ q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁
    _ _ _ _ _ _ _ _ _ _ _ _ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁ p₀ q₀ p₁ q₁
    D₀₁₀ D₀₀₁ hD₀₁₀ hne₀₁₀ hD₀₁₀Ω hD₀₀₁ hne₀₀₁ hD₀₀₁Ω
    D₁₁₀ D₁₀₁ hD₁₁₀ hne₁₁₀ hD₁₁₀Ω hD₁₀₁ hne₁₀₁ hD₁₀₁Ω _
    D₀ D₁ hD₀ hne₀ hi₀ hne₁ hi₁
  let νL := fun ψ => (rationalNormCharacters L ψ).toMul
  let νM := fun ψ => (rationalNormCharacters L ψ).toMul.comp
    e.symm.toMulEquiv.toMonoidHom
  let χM := unramifiedCharactersHomeomorph e νL
  let J₁₀ := standardInductionIntertwinerFamily
    h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A
  let J₀₁ := standardInductionIntertwinerFamily
    h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A
  let pT := transportedCompactModelContinuation
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₀ K₁ hP₀ hP₁ hK₀ hK₁
    hP₀K₀ hP₀K₁ hP₁K₀ hP₁K₁ e νL hν hr₀ hr₁ A _ J₁₀ p₀
  let qT := transportedCompactModelContinuation
    h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K₀ K₁ hP₁ hP₀ hK₀ hK₁
    hP₁K₀ hP₁K₁ hP₀K₀ hP₀K₁ e νL hν hr₁ hr₀ A _ J₀₁ q₀
  have hreplace :=
    standardInductionCompositeCanonicalRationalScalar_continuation_independent L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₁ hK₁ hP₀ hP₁ hP₀K₁ hP₁K₁ hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      p₁ q₁ hD₁₁₀ hne₁₁₀ hD₁₁₀Ω hD₁₀₁ hne₁₀₁ hD₁₀₁Ω hne₁ hi₁ pT qT
  refine Eq.trans ?_ hreplace.symm
  let s₀ := compactInductionScalarExtraction h₀ hU₀ hδ₀ K₀ hP₀ hK₀ hP₀K₀
    νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
    (χM (Classical.choose hne₀)) (hi₀ _ (Classical.choose_spec hne₀))
  let s₁ := compactInductionScalarExtraction h₀ hU₀ hδ₀ K₁ hP₀ hK₁ hP₀K₁
    νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
    (χM (Classical.choose hne₁)) (hi₁ _ (Classical.choose_spec hne₁))
  change continuedCompositeRationalScalar L hp hL p₀ q₀
      (hne₀₁₀.mono hD₀₁₀Ω) (hne₀₀₁.mono hD₀₀₁Ω) s₀.val.1 s₀.val.2 =
    continuedCompositeRationalScalar L hp hL pT qT
      (hne₁₁₀.mono hD₁₁₀Ω) (hne₁₀₁.mono hD₁₀₁Ω) s₁.val.1 s₁.val.2
  have hR := continuedCompositeRegion_nonempty L hp hL p₀ q₀
    (hne₀₁₀.mono hD₀₁₀Ω) (hne₀₀₁.mono hD₀₀₁Ω)
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hR hR (p₀.regularRegion_isOpen.inter q₀.regularRegion_isOpen) hR
    (fun _ hχ => hχ) (fun _ hχ => hχ)
  intro χ hχ
  have hc := continuedInductionComposite_compact_eq_scalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₀ hK₀ hP₀ hP₁ hP₀K₀ hP₁K₀ hr₀ hr₁ e hν A
    J₁₀ J₀₁ p₀ q₀ hD₀₁₀ hne₀₁₀ hD₀₁₀Ω hD₀₀₁ hne₀₀₁ hD₀₀₁Ω
    hD₀ hne₀ hi₀ s₀.val.1 s₀.val.2 s₀.property ⟨χ, hχ⟩
  let S := unramifiedCompactModelEquiv
    h₀ hU₀ hδ₀ K₀ K₁ hP₀ hK₀ hK₁ hP₀K₀ hP₀K₁ νM
    (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A (χM χ)
  let T := unramifiedCompactModelEquiv
    h₁ hU₁ hδ₁ K₀ K₁ hP₁ hK₀ hK₁ hP₁K₀ hP₁K₁ νM
    (fun ψ => (hν ψ).comp e.symm.continuous) hr₁ A (χM χ)
  have hconj : pT.continuedComposite qT ⟨χ, hχ⟩ =
      p₀.continuedCompositeScalar q₀ s₀.val.1 s₀.val.2 ⟨χ, hχ⟩ • LinearMap.id := by
    apply LinearMap.ext
    intro f
    obtain ⟨w, rfl⟩ := S.toLinearEquiv.surjective f
    change qT.continuedOperator ⟨χ, hχ.2⟩
      (pT.continuedOperator ⟨χ, hχ.1⟩ (S w)) = _
    have hpT : pT.continuedOperator ⟨χ, hχ.1⟩ (S w) =
        T (p₀.continuedOperator ⟨χ, hχ.1⟩ w) :=
      transportedCompactModelContinuation_continuedOperator_natural
        h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₀ K₁ hP₀ hP₁ hK₀ hK₁
        hP₀K₀ hP₀K₁ hP₁K₀ hP₁K₁ e νL hν hr₀ hr₁ A _ J₁₀ p₀ ⟨χ, hχ.1⟩ w
    have hqT : qT.continuedOperator ⟨χ, hχ.2⟩
        (T (p₀.continuedOperator ⟨χ, hχ.1⟩ w)) =
        S (q₀.continuedOperator ⟨χ, hχ.2⟩ (p₀.continuedOperator ⟨χ, hχ.1⟩ w)) :=
      transportedCompactModelContinuation_continuedOperator_natural
        h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K₀ K₁ hP₁ hP₀ hK₀ hK₁
        hP₁K₀ hP₁K₁ hP₀K₀ hP₀K₁ e νL hν hr₁ hr₀ A _ J₀₁ q₀ ⟨χ, hχ.2⟩
        (p₀.continuedOperator ⟨χ, hχ.1⟩ w)
    rw [hpT, hqT]
    change S (p₀.continuedComposite q₀ ⟨χ, hχ⟩ w) = _
    rw [hc]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    rfl
  change p₀.continuedCompositeScalar q₀ s₀.val.1 s₀.val.2 ⟨χ, hχ⟩ =
    endomorphismScalarCoefficient s₁.val.1 s₁.val.2 (pT.continuedComposite qT ⟨χ, hχ⟩)
  rw [hconj, endomorphismScalarCoefficient_smul_id s₁.val.1 s₁.val.2 s₁.property]

end Langlands.Plancherel
