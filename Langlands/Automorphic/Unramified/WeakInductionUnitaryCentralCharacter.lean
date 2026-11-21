import Langlands.Automorphic.CentralCharacterTopCoefficient
import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.Unramified.HeckeLocalComponentRigidityProof
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-! # Unitary central characters of cuspidal weak inductions -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Filter Polynomial
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open scoped NumberField

private theorem isUnitary_of_cofinite_uniformizer
    {F : Type uF} [Field F] [NumberField F] (ω : HeckeCharacter F)
    (h : ∀ᶠ v in cofinite, ω.IsUnramifiedAt v ∧ ‖(ω.finiteUniformizerValue v : ℂ)‖ = 1) :
    ω.IsUnitary := by
  let μ : HeckeCharacter F := (unitsNormRpow 1).comp ω
  have hModulus (x : IdeleClasses F) : μ x = 1 ↔ ‖(ω x : ℂ)‖ = 1 := by
    rw [← Units.val_inj]
    change ((‖(ω x : ℂ)‖ ^ (1 : ℝ) : ℝ) : ℂ) = 1 ↔ ‖(ω x : ℂ)‖ = 1
    simp
  have hfinite := eventually_cofinite.mp h
  have hμ : μ = 1 := by
    apply heckeLocalComponentRigidity F μ 1 hfinite.toFinset
    intro v hv
    have hgood : ω.IsUnramifiedAt v ∧ ‖(ω.finiteUniformizerValue v : ℂ)‖ = 1 := by
      by_contra hbad
      exact hv (hfinite.mem_toFinset.mpr hbad)
    have hIntegral : μ.IsUnramifiedAt v := by
      intro a ha
      change unitsNormRpow 1 (ω.finiteComponent v a) = 1
      rw [hgood.1 a ha, map_one]
    let G := (μ.finiteComponent v).toMonoidHom.ker
    have hG : G = ⊤ :=
      CompletionPadic.subgroup_eq_top_of_uniformizer_mem F v G
        (fun a ha => MonoidHom.mem_ker.mpr (hIntegral a ha))
        (MonoidHom.mem_ker.mpr ((hModulus _).mpr hgood.2))
    refine ⟨hIntegral, fun _ _ => rfl, ?_⟩
    apply DFunLike.ext
    intro a
    exact MonoidHom.mem_ker.mp (hG ▸ Subgroup.mem_top a : a ∈ G)
  intro x
  exact (hModulus x).mp (by rw [hμ]; rfl)

private theorem norm_leadingCoeff_eulerPolynomial
    {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} {S : CuspidalOperatorRealization F r} {ω : HeckeCharacter F}
    (hω : S.HasCentralCharacter ω) (P : CuspidalSpectralPresentation.{uF, uV} S)
    (v : FinitePlace F) (hv : v ∉ P.exceptional) :
    ‖(P.spectralSystem.eulerPolynomial v hv).leadingCoeff‖ =
      ‖(ω.finiteUniformizerValue v : ℂ)‖ := by
  rw [S.finiteUniformizerValue_eq_elementaryCoefficient v hω P hv]
  simp [SpectralSystem.eulerPolynomial, elementaryCoefficient, ← Polynomial.coeff_natDegree]

/-- A cuspidal weak induction of a cusp with unitary central character has
unitary central character. -/
def WeakInductionUnitaryCentralCharacterStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r m : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E m),
    HasUnitaryCentralCharacter T →
    S.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass →
    HasUnitaryCentralCharacter S

theorem weakInductionUnitaryCentralCharacter :
    WeakInductionUnitaryCentralCharacterStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ r m S T hT hWeak
  obtain ⟨ξ, hξunit, hξ⟩ := hT
  obtain ⟨ω, hω, _⟩ := S.realization.existsUnique_hasCentralCharacter S.irreducible
  obtain ⟨P, Q, hPQ⟩ :=
    (CuspidalOperatorRealization.IsoClass.isWeakInductionOf_isoClass_iff.{uF, uE, uV, uW}
      S T).mp hWeak
  refine ⟨ω, isUnitary_of_cofinite_uniformizer ω ?_, hω⟩
  obtain ⟨A, hA⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F ω
  filter_upwards [hPQ.2, A.eventually_cofinite_notMem] with v hv hvA
  obtain ⟨hP, hQ, _, hEuler⟩ := hv
  refine ⟨hA v hvA, ?_⟩
  rw [← norm_leadingCoeff_eulerPolynomial hω P v hP, hEuler,
    SpectralSystem.inducedEulerPolynomial, Polynomial.leadingCoeff_prod, _root_.norm_prod]
  apply Finset.prod_eq_one
  intro w _
  have hdeg : ((X : Polynomial ℂ) ^ w.1.asIdeal.inertiaDeg (𝓞 F)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_pow]
    exact (w.1.asIdeal.inertiaDeg_pos (𝓞 F)).ne'
  rw [Polynomial.leadingCoeff_comp hdeg, Polynomial.leadingCoeff_X_pow, one_pow, mul_one,
    norm_leadingCoeff_eulerPolynomial hξ Q w.1 (hQ w)]
  exact hξunit _

end Langlands.Automorphic.Unramified
