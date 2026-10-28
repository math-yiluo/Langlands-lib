import Langlands.Representation.Whittaker.TwoBlockJacquetFunctionalExtensionStatement
import Langlands.Representation.Whittaker.TwoBlockCellIntegrabilityProof
import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceProof
import Langlands.Representation.Whittaker.SubgroupFunctionalExtension
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # Extending the two-block cell integral to the actual full induction -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

/-- The integrable cell integral is a character functional on the invariant
cell subspace, and smooth localization exactness extends it to the induction. -/
theorem twoBlockJacquetFunctionalExtension :
    TwoBlockJacquetFunctionalExtensionStatement.{uF, uV} := by
  intro p _ F a b V₁ V₂ _ _ _ _ π₁ π₂
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  let := T.upperUnipotentNonarchimedean (a + 1 + (b + 1))
  dsimp only
  intro ψ ℓ₁ hℓ₁ ℓ₂ hℓ₂ μ _
  let U := upperUnipotent (a + 1 + (b + 1)) F.Carrier
  let θ := standardCharacter ψ (a + 1 + b)
  let ρ := twoBlockInduced F a b π₁ π₂
  let D := twoBlockCellSubmodule F a b π₁ π₂
  let τ : Representation ℂ U D :=
    Representation.subrepresentation (ρ.comp U.subtype) D (fun u f hf =>
      twoBlockCellUnipotentStability p F a b π₁ π₂ u f hf)
  let i : τ.IntertwiningMap (ρ.comp U.subtype) :=
    { toLinearMap := D.subtype
      isIntertwining' := fun _ => rfl }
  let ℓ := Shahidi.pairFunctional ℓ₁ ℓ₂
  let j : D →ₗ[ℂ] (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier → ℂ) :=
    (LinearMap.mulLeft ℂ (Shahidi.intertwiningJacquetKernel a b ψ)).comp
      ((ℓ.compLeft _).comp (twoBlockCellRestriction F a b π₁ π₂))
  have hj (f : D) : Integrable (j f) μ :=
    twoBlockCellJacquetIntegrability p F a b π₁ π₂ ψ ℓ μ f
  let J : D →ₗ[ℂ] ℂ :=
    { toFun f := ∫ x, j f x ∂μ
      map_add' f g := by
        simp only [map_add, Pi.add_apply]
        exact integral_add (hj f) (hj g)
      map_smul' c f := by
        simp only [map_smul, Pi.smul_apply]
        exact integral_smul c (j f) }
  have hJ : J ∈ functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) τ := by
    intro u f
    exact (twoBlockJacquetCovariance p F a b π₁ π₂ ψ
      ℓ₁ hℓ₁ ℓ₂ hℓ₂ μ f.val u.val (hj f)).2
  have hθopen : IsOpen (θ.ker : Set U) :=
    isOpen_ker_of_continuous_complex_character θ
      (standardCharacterContinuous ψ (a + 1 + b)).continuous
  have hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro u
    refine ⟨(fun v : U => u⁻¹ * v) ⁻¹' (θ.ker : Set U),
      hθopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp
    · intro v hv
      have hv' : θ (u⁻¹ * v) = 1 := hv
      have he : (θ u)⁻¹ * θ v = 1 := by
        simpa only [map_mul, map_inv] using hv'
      exact congrArg Units.val (inv_mul_eq_one.mp he).symm
  obtain ⟨L, hL⟩ := exists_functional_extension_of_subgroup_intertwiner
    U θ ρ τ (upperUnipotent_isLimitOfCompactSubgroups F T (a + 1 + (b + 1)))
    hθ i Subtype.val_injective
    (T.isSmooth_normalizedProductInduced (twoBlockShape a b) (Shahidi.pairFamily π₁ π₂))
    ⟨J, hJ⟩
  exact ⟨L, hL⟩

end Langlands.Whittaker
