import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.Correspondence.HenniartRankConductor
import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.LocalFactor.CommonClosureGenerationProof
import Langlands.LocalFactor.SpectralConductorChoice
import Langlands.LocalFactor.SpectralConductorDegree
import Langlands.LocalFactor.SpectralConductorRankOneBridge
import Langlands.LocalFactor.SpectralConductorRankOneProof
import Langlands.Representation.Category.UniverseLift

/-! # Integrality of the Artin conductor of a local Weil representation -/

noncomputable section

namespace Langlands.Henniart

open Correspondence LocalFactor.CommonClosure LocalFactor.ConductorExponent
open LocalFactor.SpectralConductor Ramification.Padic VirtualRepresentation Weil.Local

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
private theorem inductionFactor_eq_residueDegree (e : ReciprocityFamily K)
    (he : NormalizedReciprocity K e) (L : Extension K)
    (M : FiniteGaloisIntermediateField K.Carrier (AlgebraicClosure K.Carrier))
    (hLM : L.field ≤ M.toIntermediateField) :
    (Fintype.card (FiniteRepresentation.Induction.Cosets (nestedL K L)) : ℂ) *
        (Nat.card (inertiaL K M L) : ℂ) / (Nat.card (inertiaM K M) : ℂ) =
      ((residueDegreeL e L).natAbs : ℂ) := by
  have hCard : (Nat.card (inertiaL K M L) : ℂ) *
      (((fixingM K M L).subgroupOf (inertiaM K M)).index : ℂ) =
      (Nat.card (inertiaM K M) : ℂ) := by
    exact_mod_cast card_inertiaL_mul_index L M
  have hNe : (Nat.card (inertiaM K M) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := inertiaM K M)).ne'
  rw [card_cosets_nestedL, index_weilSubgroup e L he, relIndex_localInertia L M hLM]
  push_cast
  rw [mul_right_comm, mul_comm (((fixingM K M L).subgroupOf (inertiaM K M)).index : ℂ),
    hCard, mul_div_cancel_left₀ _ hNe]

private theorem presentationArtinConductor_nonneg
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (P : FiniteInertiaPresentation K A)
    (hP : Function.Surjective (weilInertiaRestriction K P.extension)) :
    0 ≤ P.artinConductor hP := by
  let T := dataM K P.extension
  let I := inertiaM K P.extension
  let := inertiaIntegerAction T K.Carrier
  let := inertiaIntegerAction_faithful' T K.Carrier
  let := integerRing_noetherian' T
  let : Finite I := inertiaM_finite K P.extension
  change 0 ≤ Ramification.artinConductor T.Integers I (P.representation hP)
  unfold Ramification.artinConductor
  exact Finset.sum_nonneg fun i _ => Ramification.conductorTerm_nonneg T.Integers I _ i

private theorem exists_integral_presentation
    (B : FiniteRepresentation.{0, uK, max uK uW} ℂ (weilSubgroup K (base K)))
    (hB : B.IsContinuous) :
    ∃ (P : Presentation.{uK, uW} K B)
      (hP : Function.Surjective (weilInertiaRestriction K P.extension)) (a : ℕ),
      P.artinConductor hP = (a : ℚ) := by
  classical
  obtain ⟨e, he⟩ := LocalClassField.commonClosureReciprocityExistence p K
    K.canonicalTopologicalData
  have hR := commonClosureRankOneConductor p K
  have hB₀ := FiniteRepresentation.isContinuous_restrict (baseInclusion K).toMonoidHom
    (baseInclusion K).continuous hB
  obtain ⟨P⟩ := Ramification.HerbrandBridge.continuousWeilFiniteInertiaPresentation K _ hB₀
  let x := baseClass K B hB
  let one := ExactGrothendieckGroup.characterClass (1 : weilSubgroup K (base K) →ₜ* ℂˣ)
  obtain ⟨S, hS, hx⟩ :=
    exists_finset_generators (LocalFactor.commonClosureDegreeZeroGeneration p K) (base K) x
  obtain ⟨M, hPM, hPresent⟩ := exists_presentingField K S hS P.extension
  have hM := Ramification.HerbrandBridge.weilInertiaRestriction_surjective K M
  let integral := (Int.castAddHom ℂ).range.comap (conductorFunctional.{uK, uW} K M)
  have hGenerator : (S : Set (Virtual.{uK, uW} K (base K))) ⊆ integral := by
    intro y hy
    obtain ⟨L, h, χ, χ', hLM, rfl, hχ, hχ'⟩ := hPresent y hy
    change ∃ z : ℤ, (z : ℂ) = conductorFunctional.{uK, uW} K M _
    refine ⟨((residueDegreeL e L).natAbs : ℤ) *
      ((characterConductor e L χ : ℤ) - (characterConductor e L χ' : ℤ)), ?_⟩
    rw [conductorFunctional_induce_eq K M L hLM h χ χ' hχ hχ',
      inductionFactor_eq_residueDegree K e he L M hLM,
      lClassSum_eq_characterConductor χ hχ hR e he,
      lClassSum_eq_characterConductor χ' hχ' hR e he]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  have hOne : one ∈ integral := by
    change ∃ z : ℤ, (z : ℂ) = conductorFunctional.{uK, uW} K M one
    exact ⟨0, by rw [Int.cast_zero, conductorFunctional_one]⟩
  have hSpan : Submodule.span ℤ (S : Set (Virtual.{uK, uW} K (base K))) ≤
      integral.toIntSubmodule := Submodule.span_le.mpr hGenerator
  have hDegreeZero : x - degree K (base K) x • one ∈ integral := hSpan hx
  have hIntegral : x ∈ integral := by
    have hSum := integral.add_mem hDegreeZero (integral.zsmul_mem hOne (degree K (base K) x))
    rwa [sub_add_cancel] at hSum
  obtain ⟨z, hz⟩ := hIntegral
  change (z : ℂ) = conductorFunctional.{uK, uW} K M (baseClass K B hB) at hz
  rw [conductorFunctional_baseClass K M B hB P hPM hM] at hz
  let Q := P.refine M hPM
  have hQ : Q.artinConductor hM = (z : ℚ) := by exact_mod_cast hz.symm
  have hzNonneg : 0 ≤ z := by
    have hh := presentationArtinConductor_nonneg K Q hM
    rw [hQ] at hh
    exact_mod_cast hh
  exact ⟨Q, hM, z.toNat, hQ.trans (by exact_mod_cast (Int.toNat_of_nonneg hzNonneg).symm)⟩

/-- Every irreducible Weil class over a p-adic field has a natural Artin conductor. -/
theorem weilArtinConductorExistence : WeilArtinConductorExistenceStatement.{uK, uW} := by
  intro p _ K k σ
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  have hClass : FiniteRepresentation.classOf A.val = weilClassForget K σ :=
    congrArg (FiniteRepresentation.forgetPropertyClass _) hA
  let B₀ := FiniteRepresentation.restrict (weilSubgroup K (base K)).subtype A.val
  let B : FiniteRepresentation.{0, uK, max uK uW} ℂ (weilSubgroup K (base K)) :=
    FiniteRepresentation.of (universeLiftRepresentation.{uK} B₀.representation)
  let eB : FiniteRepresentation.Equiv B₀ B := universeLiftEquiv.{uK} B₀.representation
  have hB₀ := FiniteRepresentation.isContinuous_restrict (weilSubgroup K (base K)).subtype
    continuous_subtype_val A.property.1
  have hB := (FiniteRepresentation.isContinuous_iff_of_equiv eB).mp hB₀
  obtain ⟨P, hP, a, ha⟩ := exists_integral_presentation K B hB
  let e : FiniteRepresentation.Equiv A.val
      (FiniteRepresentation.restrict (baseInclusion K).toMonoidHom B) :=
    Representation.Equiv.mk eB.toLinearEquiv
      (fun g => eB.toIntertwiningMap.isIntertwining' (baseInclusion K g))
  obtain ⟨Q, hQ, hArtin⟩ := Langlands.Henniart.Extension.exists_presentation_of_equiv K e.symm P hP
  exact ⟨a, A.val, Q, hQ, hClass, hArtin.trans ha⟩

end Langlands.Henniart
