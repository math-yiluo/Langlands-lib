import Langlands.Representation.Plancherel.StandardInductionScalarRepresentativeStatement
import Langlands.Representation.Plancherel.StandardInductionRepresentativeContinuation
import Langlands.Representation.Plancherel.ContinuedIntertwiningScalarNaturality

/-! # Representative independence of actual canonical standard scalars -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV uW

/-- The canonical rational scalar of the actual standard-integral composite
is unchanged by an equivalence of inducing representations, with independently
supplied continuations and independently selected canonical coefficients. -/
theorem conditionalStandardInductionScalarRepresentative :
    ConditionalStandardInductionScalarRepresentativeStatement.{u, uG, uV, uW} := by
  intro F _ _ _ _ L _ hp hL G _ _ _ _ _ P₀ P₁ M U₀ U₁
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A B φ
    _ _ _ _ _ _ _ _ _ _ _ _ q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁
    _ _ _ _ _ _ _ _ _ _ _ _ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁ pA qA pB qB
    DA₁₀ DA₀₁ hDA₁₀ hneA₁₀ hDA₁₀Ω hDA₀₁ hneA₀₁ hDA₀₁Ω
    DB₁₀ DB₀₁ hDB₁₀ hneB₁₀ hDB₁₀Ω hDB₀₁ hneB₀₁ hDB₀₁Ω _
    DA DB hDA hneA hiA hneB hiB
  let νL := fun ψ => (rationalNormCharacters L ψ).toMul
  let νM := fun ψ => (rationalNormCharacters L ψ).toMul.comp
    e.symm.toMulEquiv.toMonoidHom
  let χM := unramifiedCharactersHomeomorph e νL
  have hΩ₁₀ := standardIntertwiningFullDomainRegion_equiv
    h₀ hU₀ U₁ e νL q₁₀ φ
  have hΩ₀₁ := standardIntertwiningFullDomainRegion_equiv
    h₁ hU₁ U₀ e νL q₀₁ φ
  have hDA₁₀B : DA₁₀ ⊆ standardIntertwiningFullDomainRegion
      h₀ hU₀ U₁ e νL q₁₀ B :=
    fun _ hχ => hΩ₁₀ ▸ hDA₁₀Ω hχ
  have hDA₀₁B : DA₀₁ ⊆ standardIntertwiningFullDomainRegion
      h₁ hU₁ U₀ e νL q₀₁ B :=
    fun _ hχ => hΩ₀₁ ▸ hDA₀₁Ω hχ
  let JA₁₀ := standardInductionIntertwinerFamily
    h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A
  let JA₀₁ := standardInductionIntertwinerFamily
    h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A
  let JB₁₀ := standardInductionIntertwinerFamily
    h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ B
  let JB₀₁ := standardInductionIntertwinerFamily
    h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ B
  let sA := compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K
    νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
    (χM (Classical.choose hneA)) (hiA _ (Classical.choose_spec hneA))
  let sB := compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K
    νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ B
    (χM (Classical.choose hneB)) (hiB _ (Classical.choose_spec hneB))
  refine continuedInductionCompositeRationalScalar_representative_independent L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A B
    JA₁₀ JA₀₁ pA qA JB₁₀ JB₀₁ pB qB
    hDA₁₀ hneA₁₀ hDA₁₀Ω hDA₁₀B hDA₀₁ hneA₀₁ hDA₀₁Ω hDA₀₁B
    φ ?_ ?_ hDA hneA hiA sA.val.1 sA.val.2 sA.property
    sB.val.1 sB.val.2 sB.property
  · intro χ hχ f
    exact standardInductionIntertwinerFamily_representative_natural
      h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀
      φ ⟨χ, hDA₁₀Ω hχ⟩ f
  · intro χ hχ f
    exact standardInductionIntertwinerFamily_representative_natural
      h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁
      φ ⟨χ, hDA₀₁Ω hχ⟩ f

end Langlands.Plancherel
