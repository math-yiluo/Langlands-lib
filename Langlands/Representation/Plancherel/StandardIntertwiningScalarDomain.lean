import Langlands.Representation.Plancherel.StandardIntertwiningTarget
import Langlands.HarmonicAnalysis.SmoothScalarIntegral

/-! # Scalar convergence and the actual standard-integral domain -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- Scalar convergence at every actual evaluation point and against every
functional of the actual smooth contragredient. -/
def scalarDomain :
    Submodule ℂ ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) where
  carrier := {f | ∀ (g : G) (ℓ : SmoothDual A.representation),
    MeasureTheory.Integrable (fun q => ℓ.val (integrand h hU U' A g f q)) ν}
  zero_mem' := by
    intro g ℓ
    simp only [map_zero, Pi.zero_apply]
    exact integrable_zero _ _ _
  add_mem' := by
    intro f k hf hk g ℓ
    simp only [map_add, Pi.add_apply]
    exact (hf g ℓ).add (hk g ℓ)
  smul_mem' := by
    intro c f hf g ℓ
    simp only [map_smul, Pi.smul_apply]
    exact (hf g ℓ).smul c

@[simp]
theorem mem_scalarDomain
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    f ∈ scalarDomain h hU U' A ν ↔
      ∀ (g : G) (ℓ : SmoothDual A.representation),
        MeasureTheory.Integrable (fun q => ℓ.val (integrand h hU U' A g f q)) ν :=
  Iff.rfl

/-- Weak representability always implies scalar convergence. -/
theorem domain_le_scalarDomain :
    domain h hU U' A ν ≤ scalarDomain h hU U' A ν := by
  intro f hf g ℓ
  obtain ⟨Jf, hJf⟩ := (mem_domain h hU U' A ν f).mp hf
  exact (hJf g ℓ).1

/-- The scalar domain is stable under the original ambient right action. -/
def scalarDomainSubrepresentation :
    Subrepresentation
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation where
  toSubmodule := scalarDomain h hU U' A ν
  apply_mem_toSubmodule := by
    intro t f hf g ℓ
    rw [integrand_right_action]
    exact hf (g * t) ℓ

section CompatibleMeasure

variable [T2Space G] {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)

include hν

/-- The scalar integral has the actual source-half-character times quotient
Haar factor, without any representability assumption. -/
theorem scalarIntegral_levi_mul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (m : M) (g : G) (ℓ : SmoothDual A.representation) :
    letI : LocallyCompactSpace U' := hU'.locallyCompactSpace
    (∫ q, ℓ.val (integrand h hU U' A ((m : G) * g) f q) ∂ν) =
      ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
        ((quotientConjugationModulus h hU U' h'.levi_le_normalizer m : ℝ) : ℂ)) *
      ∫ q, (smoothContragredient A.representation m⁻¹ ℓ).val
        (integrand h hU U' A g f q) ∂ν := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let ℓm : SmoothDual A.representation :=
    smoothContragredient A.representation m⁻¹ ℓ
  have hℓm (w : A) : ℓm.val w = ℓ.val (A.representation m w) := by
    change ℓ.val (A.representation (m⁻¹)⁻¹ w) = _
    rw [inv_inv]
  have hs : (fun q => ℓ.val (integrand h hU U' A ((m : G) * g) f q)) =
      fun q => (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
        ℓm.val (integrand h hU U' A g f
          ((quotientConjugation h U' h'.levi_le_normalizer m).symm q)) := by
    funext q
    rw [integrand_levi_mul h hU U' h'.levi_le_normalizer A, map_smul, hℓm]
    rfl
  rw [hs, integral_const_mul,
    integral_quotientConjugation_symm h hU U' h'.levi_le_normalizer ν μU' μI hν m
      (fun q => ℓm.val (integrand h hU U' A g f q))]
  exact (mul_assoc _ _ _).symm

/-- Squared-modulus compatibility identifies the scalar transformation
factor with the target positive half-character. -/
theorem scalarIntegral_target_levi_mul
    (hsq : SquaredModulusCompatibility h hU h' hU')
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (m : M) (g : G) (ℓ : SmoothDual A.representation) :
    (∫ q, ℓ.val (integrand h hU U' A ((m : G) * g) f q) ∂ν) =
      (HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer m : ℂ) *
      ∫ q, (smoothContragredient A.representation m⁻¹ ℓ).val
        (integrand h hU U' A g f q) ∂ν := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  rw [scalarIntegral_levi_mul h hU U' A ν h' hU' μU' μI hν,
    leviFactor_eq_targetHalf h hU h' hU' hsq]

/-- An actual source stabilizer and the open kernel of the target character
make each scalar-integral functional a smooth bidual vector. -/
theorem scalarIntegral_open_invariant
    (hsq : SquaredModulusCompatibility h hU h' hU')
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (g : G) :
    ∃ L : OpenSubgroup M, ∀ (k : L) (ℓ : SmoothDual A.representation),
      (∫ q, (smoothContragredient A.representation (k : M) ℓ).val
        (integrand h hU U' A g f q) ∂ν) =
      ∫ q, ℓ.val (integrand h hU U' A g f q) ∂ν := by
  obtain ⟨K, hK⟩ :=
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).property f
  let c : M →* G :=
    { toFun := fun m => g⁻¹ * (m : G) * g
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_assoc] }
  have hc : Continuous c :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  let Lδ : OpenSubgroup M :=
    ⟨(HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer).ker,
      HaarModulus.isOpen_ker_closedHalfCharacter U' hU' M h'.levi_le_normalizer⟩
  let L : OpenSubgroup M := K.comap c hc ⊓ Lδ
  refine ⟨L, ?_⟩
  intro k ℓ
  let m : M := (k : M)⁻¹
  have hm : m ∈ L := L.inv_mem k.property
  have hmc : c m ∈ K := hm.1
  have hχ : HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer m = 1 :=
    hm.2
  have hg : (m : G) * g = g * c m := by simp [c, mul_assoc]
  have hkf :
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation (c m) f =
        f := hK ⟨c m, hmc⟩
  have he : integrand h hU U' A ((m : G) * g) f =
      integrand h hU U' A g f := by
    rw [hg, ← integrand_right_action, hkf]
  have ht := scalarIntegral_target_levi_mul h hU U' A ν h' hU' μU' μI hν
    hsq f m g ℓ
  rw [he, hχ, Units.val_one, one_mul] at ht
  simpa only [m, inv_inv] using ht.symm

/-- Admissibility recovers genuine weak integrability at each point from
scalar convergence on the actual quotient. -/
theorem weakIntegrable_of_mem_scalarDomain
    (hM : IsClosed (M : Set G)) (hA : A.IsAdmissible)
    (hsq : SquaredModulusCompatibility h hU h' hU')
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (hf : f ∈ scalarDomain h hU U' A ν) (g : G) :
    HarmonicAnalysis.SmoothWeakIntegral.Integrable A.representation ν
      (integrand h hU U' A g f) := by
  obtain ⟨L, hL⟩ :=
    scalarIntegral_open_invariant h hU U' A ν h' hU' μU' μI hν hsq f g
  exact HarmonicAnalysis.SmoothWeakIntegral.integrable_of_scalar_integrable_of_invariant
    A.representation ν (integrand h hU U' A g f)
    (compactCofinal hM) hA (hf g) L hL

/-- Under the existing geometric measure and modulus hypotheses, scalar
convergence is the whole actual domain; representability adds no premise. -/
theorem scalarDomain_eq_domain
    (hM : IsClosed (M : Set G)) (hA : A.IsAdmissible)
    (hsq : SquaredModulusCompatibility h hU h' hU') :
    scalarDomain h hU U' A ν = domain h hU U' A ν := by
  apply le_antisymm
  · intro f hf
    simp only [domain, Submodule.mem_iInf, Submodule.mem_comap,
      HarmonicAnalysis.SmoothWeakIntegral.mem_integrableSubmodule]
    exact weakIntegrable_of_mem_scalarDomain h hU U' A ν h' hU' μU' μI hν hM hA hsq f hf
  · exact domain_le_scalarDomain h hU U' A ν

end CompatibleMeasure

end Langlands.Plancherel.StandardIntertwining
