import Langlands.Global.AdelicAdditiveDualityStatement
import Langlands.Global.CocompactFieldRestriction
import Langlands.Global.AdelicLocalApproximation
import Langlands.Global.CocompactFieldAnnihilator
import Langlands.Global.AdelesLocallyCompactProof
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.PrincipalAdelesDiscreteProof

/-! # Assembly of actual adelic additive duality -/

noncomputable section

universe u

namespace Langlands.Global

open CocompactRingCharacters

variable (K : Type u) [Field K] [NumberField K]

private theorem fieldQuotient_compact :
    CompactSpace (Multiplicative (Adeles K) ⧸ fieldImage (diagonal K)) := by
  exact compactSpace_adeleQuotient K

private theorem fieldQuotient_hausdorff :
    T2Space (Multiplicative (Adeles K) ⧸ fieldImage (diagonal K)) := by
  let : IsClosed (fieldImage (diagonal K) : Set (Multiplicative (Adeles K))) :=
    principalAdeles_isClosed K
  infer_instance

/-- Nondegeneracy of the actual adelic multiplication pairing. -/
theorem adelicPairing_nondegenerate
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (htriv : ∀ k : K, ψ (diagonal K k) = 1) :
    ∀ a : Adeles K, (∀ x : Adeles K, ψ (a * x) = 1) → a = 0 := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_sub_diagonal_mem K
  exact CocompactPairingSeparation.nondegenerate (diagonal K) ψ.toAddChar
    ψ.continuous_toFun ψ.nontrivial htriv C hC hcover
    (AdelicLocalApproximation.exists_local_factor K)

/-- The diagonal field is its own annihilator for the actual adelic pairing. -/
theorem adelicPairing_annihilator
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (htriv : ∀ k : K, ψ (diagonal K k) = 1)
    (a : Adeles K) :
    (∀ k : K, ψ (a * diagonal K k) = 1) ↔ a ∈ Set.range (diagonal K) := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_sub_diagonal_mem K
  exact CocompactFieldAnnihilator.mem_iff_range (diagonal K) ψ.toAddChar
    ψ.continuous_toFun htriv C hC hcover (adelicPairing_nondegenerate K ψ htriv) a

/-- Every character restriction to the diagonal is a multiplication restriction. -/
theorem adelicPairing_restrictionMatching
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (htriv : ∀ k : K, ψ (diagonal K k) = 1)
    (χ : PontryaginDual (Multiplicative (Adeles K))) :
    ∃ a : Adeles K, ∀ k : K,
      χ (Multiplicative.ofAdd (diagonal K k)) = ψ (a * diagonal K k) := by
  let : TopologicalSpace K := ⊥
  let : DiscreteTopology K := ⟨rfl⟩
  let := fieldQuotient_compact K
  let := fieldQuotient_hausdorff K
  exact CocompactFieldRestriction.exists_parameter (diagonal K) ψ.toAddChar
    ψ.continuous_toFun ψ.nontrivial htriv χ

/-- The actual adelic multiplication pairing is a group homeomorphism, and the
field is its own annihilator. -/
theorem adelicDuality
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (htriv : ∀ k : K, ψ (diagonal K k) = 1) :
    (∃ e : Multiplicative (Adeles K) ≃ₜ* PontryaginDual (Multiplicative (Adeles K)),
      ∀ a x : Multiplicative (Adeles K), e a x = ψ (a.toAdd * x.toAdd)) ∧
    (∀ a : Adeles K, (∀ k : K, ψ (a * diagonal K k) = 1) ↔
      a ∈ Set.range (diagonal K)) := by
  let := fieldQuotient_compact K
  let := fieldQuotient_hausdorff K
  let := adeles_locallyCompactSpace K
  let := adeles_secondCountableTopology K
  let : SigmaCompactSpace (Adeles K) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hinj : Function.Injective
      (RingPontryaginPairing.hom ψ.toAddChar ψ.continuous_toFun) := by
    apply (injective_iff_map_eq_one (RingPontryaginPairing.hom ψ.toAddChar ψ.continuous_toFun)).mpr
    intro a ha
    have hz : a.toAdd = 0 := adelicPairing_nondegenerate K ψ htriv a.toAdd (by
      intro x
      exact congrArg (fun χ : PontryaginDual (Multiplicative (Adeles K)) =>
        χ (Multiplicative.ofAdd x)) ha)
    exact congrArg Multiplicative.ofAdd hz
  have hsurj := pairing_surjective (diagonal K) ψ.toAddChar ψ.continuous_toFun
    htriv (adelicPairing_annihilator K ψ htriv) (adelicPairing_restrictionMatching K ψ htriv)
  refine ⟨⟨RingPontryaginPairing.equivOfBijective ψ.toAddChar ψ.continuous_toFun
    ⟨hinj, hsurj⟩, ?_⟩, adelicPairing_annihilator K ψ htriv⟩
  intro a x
  rfl

/-- Actual adelic additive self-duality and the diagonal-annihilator identity. -/
theorem adelicAdditiveDuality_proof : AdelicAdditiveDualityStatement.{u} := by
  intro K _ _ ψ htriv
  exact adelicDuality K ψ htriv

end Langlands.Global
