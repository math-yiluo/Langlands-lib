import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality
import Langlands.Representation.Twist.SubquotientProof

/-!
# Formal degree without a selected central-character witness

The degree is the existing Schur-integral normalization on the unchanged
quotient and measure. Its intrinsic laws remove character-witness choices and
compare actual equivalent representations and smooth unitary twists.
-/

noncomputable section

open MeasureTheory

namespace Langlands.Plancherel

open Langlands.HarishChandraSchwartz

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

/-- The Schur formal degree, with the scalar character obtained from the
actual square-integrability witness rather than supplied as separate data. -/
def representationFormalDegree (hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ)
    (hi : ρ.IsIrreducible) : ℝ :=
  let c := Classical.choose hsq.2
  formalDegree A hA μ (χ := c.character.comp (Subgroup.inclusion hA))
    (fun a v => c.acts (Subgroup.inclusion hA a) v) hcof hsq hi

theorem representationFormalDegree_pos
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hi : ρ.IsIrreducible) :
    0 < representationFormalDegree A hA μ hcof hsq hi := by
  unfold representationFormalDegree
  exact formalDegree_pos _ _ _ _ _ _ _

/-- The characterization holds for every scalar-action witness on `A`. -/
theorem orthogonalityIntegral_eq_representationFormalDegree
    {χ : A →* ℂˣ} (h : ∀ (a : A) (v : V), ρ a v = (χ a : ℂ) • v)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hi : ρ.IsIrreducible)
    (v₁ : V) (ℓ₁ : SmoothDual ρ) (v₂ : V) (ℓ₂ : SmoothDual ρ) :
    orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ =
      (representationFormalDegree A hA μ hcof hsq hi : ℂ)⁻¹ *
        ℓ₂.val v₁ * ℓ₁.val v₂ := by
  unfold representationFormalDegree
  let c := Classical.choose hsq.2
  exact orthogonalityIntegral_eq_formalDegree A hA μ
    (χ := c.character.comp (Subgroup.inclusion hA))
    (fun a v => c.acts (Subgroup.inclusion hA a) v) hcof hsq hi v₁ ℓ₁ v₂ ℓ₂

/-- Identification with the pre-existing degree for any chosen scalar action. -/
theorem representationFormalDegree_eq_formalDegree
    {χ : A →* ℂˣ} (h : ∀ (a : A) (v : V), ρ a v = (χ a : ℂ) • v)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hi : ρ.IsIrreducible) :
    representationFormalDegree A hA μ hcof hsq hi =
      formalDegree A hA μ h hcof hsq hi :=
  formalDegree_unique A hA μ h hcof hsq hi
    (orthogonalityIntegral_eq_representationFormalDegree A hA μ hcof h hsq hi)
    (orthogonalityIntegral_eq_formalDegree A hA μ h hcof hsq hi)

omit [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] [μ.IsInvInvariant] in
/-- Pull back the actual smooth functionals and vectors through an equivalence.
The two scalar characters used to descend the integrands can differ. -/
theorem orthogonalityIntegral_equiv
    {χ : A →* ℂˣ} (hρ : ∀ (a : A) (v : V), ρ a v = (χ a : ℂ) • v)
    {η : A →* ℂˣ} (hσ : ∀ (a : A) (w : W), σ a w = (η a : ℂ) • w)
    (e : ρ.Equiv σ) (w₁ : W) (ℓ₁ : SmoothDual σ) (w₂ : W) (ℓ₂ : SmoothDual σ) :
    orthogonalityIntegral A μ hσ hσ w₁ ℓ₁ w₂ ℓ₂ =
      orthogonalityIntegral A μ hρ hρ (e.symm w₁)
        (contragredientMap e.toIntertwiningMap ℓ₁) (e.symm w₂)
        (contragredientMap e.toIntertwiningMap ℓ₂) := by
  unfold orthogonalityIntegral
  congr 1
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁.val (σ g w₁) * ℓ₂.val (σ g⁻¹ w₂) =
    ℓ₁.val (e.toIntertwiningMap (ρ g (e.symm w₁))) *
      ℓ₂.val (e.toIntertwiningMap (ρ g⁻¹ (e.symm w₂)))
  rw [e.toIntertwiningMap.isIntertwining, e.toIntertwiningMap.isIntertwining]
  simp only [Representation.Equiv.coe_toIntertwiningMap, e.apply_symm_apply]

/-- Equivalence invariance on the same quotient with the same measure. -/
theorem representationFormalDegree_equiv
    (e : ρ.Equiv σ)
    (hsqρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hiρ : ρ.IsIrreducible)
    (hsqσ : IsSquareIntegrableModCentralSubgroup A hA σ μ) (hiσ : σ.IsIrreducible) :
    representationFormalDegree A hA μ hcof hsqσ hiσ =
      representationFormalDegree A hA μ hcof hsqρ hiρ := by
  let cρ := Classical.choose hsqρ.2
  let cσ := Classical.choose hsqσ.2
  let hρ : ∀ (a : A) (v : V), ρ a v =
      ((cρ.character.comp (Subgroup.inclusion hA)) a : ℂ) • v :=
    fun a v => cρ.acts (Subgroup.inclusion hA a) v
  let hσ : ∀ (a : A) (w : W), σ a w =
      ((cσ.character.comp (Subgroup.inclusion hA)) a : ℂ) • w :=
    fun a w => cσ.acts (Subgroup.inclusion hA a) w
  apply formalDegree_unique A hA μ hσ hcof hsqσ hiσ
    (orthogonalityIntegral_eq_representationFormalDegree A hA μ hcof hσ hsqσ hiσ)
  intro w₁ ℓ₁ w₂ ℓ₂
  rw [orthogonalityIntegral_equiv A μ hρ hσ e,
    orthogonalityIntegral_eq_representationFormalDegree A hA μ hcof hρ hsqρ hiρ]
  change _ * ℓ₂.val (e (e.symm w₁)) * ℓ₁.val (e (e.symm w₂)) = _
  rw [e.apply_symm_apply, e.apply_symm_apply]

omit [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] [μ.IsInvInvariant] in
/-- A scalar twist cancels between `g` and `g⁻¹` in the bilinear Schur
integrand. The smooth-dual comparison preserves the underlying functionals. -/
theorem orthogonalityIntegral_twist
    {η : A →* ℂˣ} (hρ : ∀ (a : A) (v : V), ρ a v = (η a : ℂ) • v)
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    {ζ : A →* ℂˣ} (hτ : ∀ (a : A) (v : V), twist χ ρ a v = (ζ a : ℂ) • v)
    (v₁ : V) (ℓ₁ : SmoothDual (twist χ ρ)) (v₂ : V) (ℓ₂ : SmoothDual (twist χ ρ)) :
    orthogonalityIntegral A μ hτ hτ v₁ ℓ₁ v₂ ℓ₂ =
      orthogonalityIntegral A μ hρ hρ v₁
        (smoothContragredientTwistEquiv χ ρ hχ ℓ₁) v₂
        (smoothContragredientTwistEquiv χ ρ hχ ℓ₂) := by
  unfold orthogonalityIntegral
  congr 1
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁.val ((χ g : ℂ) • ρ g v₁) * ℓ₂.val ((χ g⁻¹ : ℂ) • ρ g⁻¹ v₂) =
    ℓ₁.val (ρ g v₁) * ℓ₂.val (ρ g⁻¹ v₂)
  simp only [map_smul, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val]
  rw [mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

/-- Smooth norm-one twists preserve the constructed Schur normalization. -/
theorem representationFormalDegree_unitaryTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hi : ρ.IsIrreducible) :
    representationFormalDegree A hA μ hcof
      (isSquareIntegrableModCentralSubgroup_unitaryTwist A hA χ hχ hu μ hsq)
      ((isIrreducible_twist_iff χ ρ).mpr hi) =
        representationFormalDegree A hA μ hcof hsq hi := by
  let hsqτ := isSquareIntegrableModCentralSubgroup_unitaryTwist A hA χ hχ hu μ hsq
  let hiτ := (isIrreducible_twist_iff χ ρ).mpr hi
  let cρ := Classical.choose hsq.2
  let cτ := Classical.choose hsqτ.2
  let hρ : ∀ (a : A) (v : V), ρ a v =
      ((cρ.character.comp (Subgroup.inclusion hA)) a : ℂ) • v :=
    fun a v => cρ.acts (Subgroup.inclusion hA a) v
  let hτ : ∀ (a : A) (v : V), twist χ ρ a v =
      ((cτ.character.comp (Subgroup.inclusion hA)) a : ℂ) • v :=
    fun a v => cτ.acts (Subgroup.inclusion hA a) v
  apply formalDegree_unique A hA μ hτ hcof hsqτ hiτ
    (orthogonalityIntegral_eq_representationFormalDegree A hA μ hcof hτ hsqτ hiτ)
  intro v₁ ℓ₁ v₂ ℓ₂
  rw [orthogonalityIntegral_twist A μ hρ χ hχ hτ,
    orthogonalityIntegral_eq_representationFormalDegree A hA μ hcof hρ hsq hi]
  rfl

end Langlands.Plancherel
