import Langlands.Representation.Plancherel.CompactInducedHermitianForm
import Langlands.Representation.Plancherel.CoefficientTensorForm

/-!
# The actual compact integral duality preserves the Hermitian dual form

The comparison is proved from pointwise Hermitian functionals and the defining
compact integral, without irreducibility of the induced representation.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands.Plancherel.CompactInduction

open Aubert.General HarishChandraSchwartz

universe uG uV

section Pointwise

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- Pointwise Hermitian functionals give a conjugate-linear map between the
two actual normalized inductions. The positive real half modulus commutes
with conjugation. -/
def hermitianMap (b : InvariantPositiveForm A.representation) :
    ((normalizedInductionFunctor h hU).obj A) →ₗ⋆[ℂ]
      ((normalizedInductionFunctor h hU).obj A.contragredient) where
  toFun f := by
    let L := Classical.choose f.property
    have hL := Classical.choose_spec f.property
    refine Induction.smoothFunctionOf P (inducingRepresentation h hU A.contragredient)
      (fun x => b.toSmoothDual A.isSmooth
        (Induction.eval P (inducingRepresentation h hU A) f x)) ?_ L ?_
    · intro q x
      rw [normalizedInductionFunctor_covariant, (b.toSmoothDual A.isSmooth).map_smulₛₗ,
        b.toSmoothDual_apply_action]
      have hreal :
          conj ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) =
            ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) := by
        simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter_apply,
          Complex.conj_ofReal]
      rw [hreal]
      rfl
    · intro l x
      exact congrArg (b.toSmoothDual A.isSmooth)
        (congrArg (fun F : Induction.EquivariantFunctions P
          (inducingRepresentation h hU A) => F.1 x) (hL l))
  map_add' f j := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add (b.toSmoothDual A.isSmooth) _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (b.toSmoothDual A.isSmooth).map_smulₛₗ c _

@[simp]
theorem hermitianMap_eval (b : InvariantPositiveForm A.representation)
    (f : (normalizedInductionFunctor h hU).obj A) (x : G) :
    Induction.eval P (inducingRepresentation h hU A.contragredient)
      (hermitianMap h hU A b f) x =
        b.toSmoothDual A.isSmooth (Induction.eval P (inducingRepresentation h hU A) f x) := rfl

end Pointwise

section Integral

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- The pointwise Hermitian map is an anti-isometry for the exact compact
probability forms on the two induced factors. -/
theorem hermitianMap_inner (hcof : CompactOpenCofinal M)
    (hA : IsAdmissible A.representation) (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A) :
    (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
      (dualInvariantForm b hcof hA)).inner
        (hermitianMap h hU A b f) (hermitianMap h hU A b j) =
      (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner j f := by
  change (∫ k : K, (dualInvariantForm b hcof hA).inner
    (Induction.eval P (inducingRepresentation h hU A.contragredient)
      (hermitianMap h hU A b f) k)
    (Induction.eval P (inducingRepresentation h hU A.contragredient)
      (hermitianMap h hU A b j) k) ∂measure K hK) =
    ∫ k : K, b.inner (Induction.eval P (inducingRepresentation h hU A) j k)
      (Induction.eval P (inducingRepresentation h hU A) f k) ∂measure K hK
  apply integral_congr_ae
  filter_upwards with k
  change b.inner
    ((b.smoothDualEquiv hcof hA).symm
      (b.smoothDualEquiv hcof hA (Induction.eval P (inducingRepresentation h hU A) j k)))
    ((b.smoothDualEquiv hcof hA).symm
      (b.smoothDualEquiv hcof hA (Induction.eval P (inducingRepresentation h hU A) f k))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

variable [T2Space G] (hm : Continuous h.projection)

include K hK hPK hm in
omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] [T2Space G] in
/-- Compact representatives discharge the compact-quotient premise of the
existing admissibility theorem for actual normalized induction. -/
theorem induced_isAdmissible (hA : A.IsAdmissible) :
    ((normalizedInductionFunctor h hU).obj A).IsAdmissible := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  exact normalizedInductionFunctor_obj_isAdmissible h hU hm A hA

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual compact integral dual equivalence carries an induced Hermitian
functional to the pointwise Hermitian section. -/
theorem integralDualEquiv_toSmoothDual (hA : A.IsAdmissible)
    (b : InvariantPositiveForm A.representation)
    (f : (normalizedInductionFunctor h hU).obj A) :
    integralDualEquiv h hU hP hm K hK hPK hG hδ A hA
        ((invariantPositiveForm h hU hP K hK hPK hG hδ A b).toSmoothDual
          ((normalizedInductionFunctor h hU).obj A).isSmooth f) =
      hermitianMap h hU A b f := by
  let E := integralDualEquiv h hU hP hm K hK hPK hG hδ A hA
  apply E.toLinearEquiv.symm.injective
  change E.toLinearEquiv.symm (E.toLinearEquiv _) = E.toLinearEquiv.symm _
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  apply LinearMap.ext
  intro j
  change (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j =
    smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation
      ((integralDualEquiv h hU hP hm K hK hPK hG hδ A hA).symm
        (hermitianMap h hU A b f)) j
  rw [integralDualEquiv_pairing h hU hP hm K hK hPK hG hδ A hA _ j,
    Representation.Equiv.apply_symm_apply]
  rfl

/-- Pullback by the existing compact integral duality is exactly the
Hermitian dual of the compact induced form. -/
theorem integralDualEquiv_form (hcof : CompactOpenCofinal M)
    (hcofG : CompactOpenCofinal G) (hA : A.IsAdmissible)
    (b : InvariantPositiveForm A.representation) :
    (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
      (dualInvariantForm b hcof hA)).ofEquiv
        (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA) =
      dualInvariantForm (invariantPositiveForm h hU hP K hK hPK hG hδ A b)
        hcofG (induced_isAdmissible h hU K hK hPK A hm hA) := by
  let B := invariantPositiveForm h hU hP K hK hPK hG hδ A b
  let R := B.smoothDualEquiv hcofG (induced_isAdmissible h hU K hK hPK A hm hA)
  apply InvariantPositiveForm.ext_inner
  intro ℓ m
  obtain ⟨f, rfl⟩ := R.surjective ℓ
  obtain ⟨j, rfl⟩ := R.surjective m
  change (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
    (dualInvariantForm b hcof hA)).inner
      (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA (R f))
      (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA (R j)) =
    B.inner (R.symm (R j)) (R.symm (R f))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  change (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
    (dualInvariantForm b hcof hA)).inner
      (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA
        (B.toSmoothDual ((normalizedInductionFunctor h hU).obj A).isSmooth f))
      (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA
        (B.toSmoothDual ((normalizedInductionFunctor h hU).obj A).isSmooth j)) = B.inner j f
  rw [integralDualEquiv_toSmoothDual, integralDualEquiv_toSmoothDual]
  exact hermitianMap_inner h hU hP K hK hPK hG hδ A hcof hA b f j

end Integral

end Langlands.Plancherel.CompactInduction
