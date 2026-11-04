import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Langlands.Representation.Smooth.Contragredient.WeakIntertwiner
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Unitary.SquareIntegrableProof
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Schur orthogonality and the formal degree (Waldspurger III.1 (2), (3))

For irreducible admissible representations `π₁`, `π₂` that are square integrable modulo a
central subgroup `A` and act on `A` by the same character, Waldspurger (III.1, p. 265) sets

`I(v₁, ℓ₁, v₂, ℓ₂) = ∫_{G/A} ⟨π₁(g) v₁, ℓ₁⟩ ⟨v₂, π̌₂(g) ℓ₂⟩ dg`,

where `⟨v₂, π̌₂(g) ℓ₂⟩ = ℓ₂(π₂(g⁻¹) v₂)`, and proves: (2) `I = 0` if `π₁ ≇ π₂`; (3) if
`π₁ = π₂` there is a real `d(π₁) > 0` with `I = d(π₁)⁻¹ ⟨v₁, ℓ₂⟩ ⟨v₂, ℓ₁⟩`.

This module proves both statements for a Haar measure on `G/A` that is invariant under
inversion, when every open subgroup of `G` contains a compact open subgroup. On the way it
constructs a `G`-invariant positive definite Hermitian form on an irreducible representation
that is square integrable modulo `A` (the unitarity part of Lemma III.1.3 in this case).
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe u v w

section Measure

variable {Q : Type u} [Group Q] [MeasurableSpace Q] [MeasurableMul Q] [MeasurableInv Q]
  {μ : Measure Q} [μ.IsMulLeftInvariant] [μ.IsInvInvariant]

/-- For a left invariant measure that is invariant under inversion, integrals are invariant
under right translation. -/
theorem integral_mul_right_eq_self_of_inv (F : Q → ℂ) (x : Q) :
    ∫ q, F (q * x) ∂μ = ∫ q, F q ∂μ := by
  rw [← integral_inv_eq_self (fun q => F (q * x)) μ]
  have h : ∀ q : Q, F (q⁻¹ * x) = (fun q => F q⁻¹) (x⁻¹ * q) := fun q => by
    simp [mul_inv_rev]
  simp_rw [h]
  rw [integral_mul_left_eq_self (fun q => F q⁻¹) x⁻¹, integral_inv_eq_self F μ]

end Measure

section Integrand

variable {G : Type u} [Group G] (A : Subgroup G)
  {V₁ : Type v} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type w} [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ G V₁} {π₂ : Representation ℂ G V₂} {χ : A →* ℂˣ}

/-- The integrand of Waldspurger's `I(v₁, ℓ₁, v₂, ℓ₂)` on `G`:
`g ↦ ℓ₁(π₁(g) v₁) ℓ₂(π₂(g⁻¹) v₂)`. -/
def orthogonalityFun (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂)
    (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂) (ℓ₂ : Module.Dual ℂ V₂) (g : G) : ℂ :=
  ℓ₁ (π₁ g v₁) * ℓ₂ (π₂ g⁻¹ v₂)

theorem orthogonalityFun_mul (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
    (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x) (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁)
    (v₂ : V₂) (ℓ₂ : Module.Dual ℂ V₂) (g : G) (a : A) :
    orthogonalityFun π₁ π₂ v₁ ℓ₁ v₂ ℓ₂ (g * (a : G)) = orthogonalityFun π₁ π₂ v₁ ℓ₁ v₂ ℓ₂ g := by
  unfold orthogonalityFun
  have e₁ : π₁ (g * a) v₁ = (χ a : ℂ) • π₁ g v₁ := by
    rw [map_mul, Module.End.mul_apply, h₁, map_smul]
  have e₂ : π₂ (g * a)⁻¹ v₂ = (χ a⁻¹ : ℂ) • π₂ g⁻¹ v₂ := by
    rw [mul_inv_rev, map_mul, Module.End.mul_apply, show ((a : G))⁻¹ = ((a⁻¹ : A) : G) from rfl,
      h₂]
  rw [e₁, e₂, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val,
    mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

/-- Waldspurger's integrand as a function on `G/A`. It is well defined because `π₁` and `π₂`
act on `A` by the same character `χ`. -/
def orthogonalityIntegrand (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
    (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x) (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁)
    (v₂ : V₂) (ℓ₂ : Module.Dual ℂ V₂) : G ⧸ A → ℂ :=
  Quotient.lift (orthogonalityFun π₁ π₂ v₁ ℓ₁ v₂ ℓ₂) (by
    intro x y hxy
    have hz : x⁻¹ * y ∈ A := QuotientGroup.leftRel_apply.mp hxy
    have h := orthogonalityFun_mul A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ x ⟨x⁻¹ * y, hz⟩
    simpa using h.symm)

variable (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x)

@[simp]
theorem orthogonalityIntegrand_mk (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂)
    (ℓ₂ : Module.Dual ℂ V₂) (g : G) :
    orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ (QuotientGroup.mk g) =
      ℓ₁ (π₁ g v₁) * ℓ₂ (π₂ g⁻¹ v₂) := rfl

theorem orthogonalityIntegrand_add_left (v₁ v₁' : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂)
    (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ (v₁ + v₁') ℓ₁ v₂ ℓ₂ =
      orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ +
        orthogonalityIntegrand A h₁ h₂ v₁' ℓ₁ v₂ ℓ₂ := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [Pi.add_apply]
  change ℓ₁ (π₁ _ (v₁ + v₁')) * _ = ℓ₁ (π₁ _ v₁) * _ + ℓ₁ (π₁ _ v₁') * _
  rw [map_add, map_add, add_mul]

theorem orthogonalityIntegrand_smul_left (c : ℂ) (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂)
    (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ (c • v₁) ℓ₁ v₂ ℓ₂ =
      fun q => c * orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁ (π₁ _ (c • v₁)) * _ = c * (ℓ₁ (π₁ _ v₁) * _)
  rw [map_smul, map_smul, smul_eq_mul, mul_assoc]

theorem orthogonalityIntegrand_add_right (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂)
    (ℓ₂ ℓ₂' : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ (ℓ₂ + ℓ₂') =
      orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ +
        orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂' := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [Pi.add_apply]
  change _ * (ℓ₂ + ℓ₂') _ = _ * ℓ₂ _ + _ * ℓ₂' _
  rw [LinearMap.add_apply, mul_add]

theorem orthogonalityIntegrand_smul_right (c : ℂ) (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂)
    (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ (c • ℓ₂) =
      fun q => c * orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change _ * (c • ℓ₂) _ = c * (_ * ℓ₂ _)
  rw [LinearMap.smul_apply, smul_eq_mul]
  ring

theorem orthogonalityIntegrand_add_left_dual (v₁ : V₁) (ℓ₁ ℓ₁' : Module.Dual ℂ V₁) (v₂ : V₂)
    (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ v₁ (ℓ₁ + ℓ₁') v₂ ℓ₂ =
      orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ +
        orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁' v₂ ℓ₂ := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [Pi.add_apply]
  change (ℓ₁ + ℓ₁') _ * _ = ℓ₁ _ * _ + ℓ₁' _ * _
  rw [LinearMap.add_apply, add_mul]

theorem orthogonalityIntegrand_smul_left_dual (c : ℂ) (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁)
    (v₂ : V₂) (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ v₁ (c • ℓ₁) v₂ ℓ₂ =
      fun q => c * orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change (c • ℓ₁) _ * _ = c * (ℓ₁ _ * _)
  rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc]

theorem orthogonalityIntegrand_add_right_vec (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁) (v₂ v₂' : V₂)
    (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ (v₂ + v₂') ℓ₂ =
      orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ +
        orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂' ℓ₂ := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [Pi.add_apply]
  change _ * ℓ₂ (π₂ _ (v₂ + v₂')) = _ * ℓ₂ (π₂ _ v₂) + _ * ℓ₂ (π₂ _ v₂')
  rw [map_add, map_add, mul_add]

theorem orthogonalityIntegrand_smul_right_vec (c : ℂ) (v₁ : V₁) (ℓ₁ : Module.Dual ℂ V₁)
    (v₂ : V₂) (ℓ₂ : Module.Dual ℂ V₂) :
    orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ (c • v₂) ℓ₂ =
      fun q => c * orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change _ * ℓ₂ (π₂ _ (c • v₂)) = c * (_ * ℓ₂ (π₂ _ v₂))
  rw [map_smul, map_smul, smul_eq_mul]
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_orthogonalityIntegrand (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (v₁ : V₁)
    (ℓ₁ : Module.Dual ℂ V₁) (v₂ : V₂) (ℓ₂ : Module.Dual ℂ V₂) :
    Continuous (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂) := by
  have c₁ : Continuous fun g : G => ℓ₁ (π₁ g v₁) :=
    (matrixCoefficient_isLocallyConstant π₁ ℓ₁ v₁ (hπ₁ v₁)).continuous
  have c₂ : Continuous fun g : G => ℓ₂ (π₂ g v₂) :=
    (matrixCoefficient_isLocallyConstant π₂ ℓ₂ v₂ (hπ₂ v₂)).continuous
  have c : Continuous (orthogonalityFun π₁ π₂ v₁ ℓ₁ v₂ ℓ₂) :=
    c₁.mul (c₂.comp continuous_inv)
  exact c.quotient_lift _

end Integrand

section Integral

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V₁ : Type v} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type w} [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ G V₁} {π₂ : Representation ℂ G V₂} {χ : A →* ℂˣ}
  (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x)

/-- Waldspurger's integrand is integrable on `G/A` (the convergence statement of III.1). -/
theorem integrable_orthogonalityIntegrand
    (hsq₁ : IsSquareIntegrableModCentralSubgroup A hA π₁ μ)
    (hsq₂ : IsSquareIntegrableModCentralSubgroup A hA π₂ μ)
    (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) (ℓ₂ : SmoothDual π₂) :
    Integrable (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ ℓ₂.val) μ := by
  obtain ⟨hadm₁, c₁, hc₁⟩ := hsq₁
  obtain ⟨hadm₂, c₂, hc₂⟩ := hsq₂
  have m₁ := hc₁ ℓ₁ v₁
  have m₂ : MemLp (fun q => centralSubgroupCoefficientNorm A hA c₂ ℓ₂ v₂ q⁻¹) 2 μ :=
    (hc₂ ℓ₂ v₂).comp_measurePreserving (Measure.measurePreserving_inv μ)
  have hint := m₁.integrable_mul m₂
  refine hint.mono'
    (continuous_orthogonalityIntegrand A h₁ h₂ hadm₁.1 hadm₂.1 v₁ ℓ₁.val v₂
      ℓ₂.val).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ‖ℓ₁.val (π₁ g v₁) * ℓ₂.val (π₂ g⁻¹ v₂)‖ ≤
    centralSubgroupCoefficientNorm A hA c₁ ℓ₁ v₁ (QuotientGroup.mk g) *
      centralSubgroupCoefficientNorm A hA c₂ ℓ₂ v₂ (QuotientGroup.mk g)⁻¹
  rw [← QuotientGroup.mk_inv, centralSubgroupCoefficientNorm_mk,
    centralSubgroupCoefficientNorm_mk, norm_mul]
  exact le_rfl

/-- Waldspurger's `I(v₁, ℓ₁, v₂, ℓ₂) = ∫_{G/A} ℓ₁(π₁(g) v₁) ℓ₂(π₂(g⁻¹) v₂) dg` (III.1,
p. 265). -/
def orthogonalityIntegral (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) (ℓ₂ : SmoothDual π₂) : ℂ :=
  ∫ q, orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ ℓ₂.val q ∂μ

/-- The first invariance of `I`: `I(π₁(h) v₁, ℓ₁, v₂, ℓ₂) = I(v₁, ℓ₁, v₂, π̃₂(h⁻¹) ℓ₂)`. -/
theorem orthogonalityIntegral_rho_left (h : G) (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂)
    (ℓ₂ : SmoothDual π₂) :
    orthogonalityIntegral A μ h₁ h₂ (π₁ h v₁) ℓ₁ v₂ ℓ₂ =
      orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ (smoothContragredient π₂ h⁻¹ ℓ₂) := by
  unfold orthogonalityIntegral
  rw [← integral_mul_right_eq_self_of_inv
    (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ (smoothContragredient π₂ h⁻¹ ℓ₂).val)
    (QuotientGroup.mk h : G ⧸ A)]
  congr 1
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁.val (π₁ g (π₁ h v₁)) * ℓ₂.val (π₂ g⁻¹ v₂) =
    ℓ₁.val (π₁ (g * h) v₁) * ℓ₂.val (π₂ h⁻¹⁻¹ (π₂ (g * h)⁻¹ v₂))
  simp only [map_mul, Module.End.mul_apply, mul_inv_rev, inv_inv,
    Representation.self_inv_apply]

omit [μ.IsInvInvariant] in
/-- The second invariance of `I`: `I(v₁, ℓ₁, π₂(h) v₂, ℓ₂) = I(v₁, π̃₁(h⁻¹) ℓ₁, v₂, ℓ₂)`. -/
theorem orthogonalityIntegral_rho_right (h : G) (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂)
    (ℓ₂ : SmoothDual π₂) :
    orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ (π₂ h v₂) ℓ₂ =
      orthogonalityIntegral A μ h₁ h₂ v₁ (smoothContragredient π₁ h⁻¹ ℓ₁) v₂ ℓ₂ := by
  unfold orthogonalityIntegral
  rw [← integral_mul_left_eq_self
    (orthogonalityIntegrand A h₁ h₂ v₁ (smoothContragredient π₁ h⁻¹ ℓ₁).val v₂ ℓ₂.val)
    (QuotientGroup.mk h⁻¹ : G ⧸ A)]
  congr 1
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁.val (π₁ g v₁) * ℓ₂.val (π₂ g⁻¹ (π₂ h v₂)) =
    ℓ₁.val (π₁ h⁻¹⁻¹ (π₁ (h⁻¹ * g) v₁)) * ℓ₂.val (π₂ (h⁻¹ * g)⁻¹ v₂)
  simp only [map_mul, Module.End.mul_apply, mul_inv_rev, inv_inv,
    Representation.self_inv_apply]

end Integral

section Forms

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal]
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V₁ : Type v} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type w} [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ G V₁} {π₂ : Representation ℂ G V₂} {χ : A →* ℂˣ}
  (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x)
  (hint : ∀ (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) (ℓ₂ : SmoothDual π₂),
    Integrable (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ ℓ₂.val) μ)

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] [μ.IsInvInvariant] in
/-- For fixed `ℓ₁` and `v₂`, the bilinear form `(v₁, ℓ₂) ↦ I(v₁, ℓ₁, v₂, ℓ₂)`. -/
def orthogonalityFormLeft (ℓ₁ : SmoothDual π₁) (v₂ : V₂) :
    V₁ →ₗ[ℂ] SmoothDual π₂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun v₁ ℓ₂ => orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂)
    (fun v₁ v₁' ℓ₂ => by
      unfold orthogonalityIntegral
      rw [orthogonalityIntegrand_add_left]
      exact integral_add (hint v₁ ℓ₁ v₂ ℓ₂)
        (hint v₁' ℓ₁ v₂ ℓ₂))
    (fun c v₁ ℓ₂ => by
      unfold orthogonalityIntegral
      rw [orthogonalityIntegrand_smul_left, integral_const_mul, smul_eq_mul])
    (fun v₁ ℓ₂ ℓ₂' => by
      unfold orthogonalityIntegral
      change ∫ q, orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ (ℓ₂.val + ℓ₂'.val) q ∂μ = _
      rw [orthogonalityIntegrand_add_right]
      exact integral_add (hint v₁ ℓ₁ v₂ ℓ₂)
        (hint v₁ ℓ₁ v₂ ℓ₂'))
    (fun c v₁ ℓ₂ => by
      unfold orthogonalityIntegral
      change ∫ q, orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ (c • ℓ₂.val) q ∂μ = _
      rw [orthogonalityIntegrand_smul_right, integral_const_mul, smul_eq_mul])

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] [μ.IsInvInvariant] in
/-- For fixed `v₁` and `ℓ₂`, the bilinear form `(v₂, ℓ₁) ↦ I(v₁, ℓ₁, v₂, ℓ₂)`. -/
def orthogonalityFormRight (v₁ : V₁) (ℓ₂ : SmoothDual π₂) :
    V₂ →ₗ[ℂ] SmoothDual π₁ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun v₂ ℓ₁ => orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂)
    (fun v₂ v₂' ℓ₁ => by
      unfold orthogonalityIntegral
      rw [orthogonalityIntegrand_add_right_vec]
      exact integral_add (hint v₁ ℓ₁ v₂ ℓ₂)
        (hint v₁ ℓ₁ v₂' ℓ₂))
    (fun c v₂ ℓ₁ => by
      unfold orthogonalityIntegral
      rw [orthogonalityIntegrand_smul_right_vec, integral_const_mul, smul_eq_mul])
    (fun v₂ ℓ₁ ℓ₁' => by
      unfold orthogonalityIntegral
      change ∫ q, orthogonalityIntegrand A h₁ h₂ v₁ (ℓ₁.val + ℓ₁'.val) v₂ ℓ₂.val q ∂μ = _
      rw [orthogonalityIntegrand_add_left_dual]
      exact integral_add (hint v₁ ℓ₁ v₂ ℓ₂)
        (hint v₁ ℓ₁' v₂ ℓ₂))
    (fun c v₂ ℓ₁ => by
      unfold orthogonalityIntegral
      change ∫ q, orthogonalityIntegrand A h₁ h₂ v₁ (c • ℓ₁.val) v₂ ℓ₂.val q ∂μ = _
      rw [orthogonalityIntegrand_smul_left_dual, integral_const_mul, smul_eq_mul])

variable (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hcof hint in
/-- For fixed `ℓ₁`, `v₂` there is an intertwiner `T : π₁ → π₂` with
`ℓ₂(T v₁) = I(v₁, ℓ₁, v₂, ℓ₂)`. -/
theorem exists_intertwiningMap_orthogonalityIntegral_left (hπ₁ : IsAdmissible π₁)
    (hπ₂ : IsAdmissible π₂) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) :
    ∃ T : π₁.IntertwiningMap π₂, ∀ (v₁ : V₁) (ℓ₂ : SmoothDual π₂),
      smoothDualPairing π₂ ℓ₂ (T v₁) = orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ :=
  exists_intertwiningMap_of_weakForm_of_compact_cofinal hcof hπ₁.1 hπ₂
    (orthogonalityFormLeft A μ h₁ h₂ hint ℓ₁ v₂)
    (fun h y ℓ => orthogonalityIntegral_rho_left A μ h₁ h₂ h y ℓ₁ v₂ ℓ)

omit [μ.IsInvInvariant] in
include hcof hint in
/-- For fixed `v₁`, `ℓ₂` there is an intertwiner `T : π₂ → π₁` with
`ℓ₁(T v₂) = I(v₁, ℓ₁, v₂, ℓ₂)`. -/
theorem exists_intertwiningMap_orthogonalityIntegral_right (hπ₁ : IsAdmissible π₁)
    (hπ₂ : IsAdmissible π₂) (v₁ : V₁) (ℓ₂ : SmoothDual π₂) :
    ∃ T : π₂.IntertwiningMap π₁, ∀ (v₂ : V₂) (ℓ₁ : SmoothDual π₁),
      smoothDualPairing π₁ ℓ₁ (T v₂) = orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ :=
  exists_intertwiningMap_of_weakForm_of_compact_cofinal hcof hπ₂.1 hπ₁
    (orthogonalityFormRight A μ h₁ h₂ hint v₁ ℓ₂)
    (fun h y ℓ => orthogonalityIntegral_rho_right A μ h₁ h₂ h v₁ ℓ y ℓ₂)

include hcof hint in
/-- **Waldspurger III.1 (2)**, in the form with integrability as a hypothesis (as in its
extension to tempered `π₂` on p. 275): if the irreducible admissible representations `π₁`, `π₂`
are not equivalent and all integrands are integrable, then `I(v₁, ℓ₁, v₂, ℓ₂) = 0`. -/
theorem orthogonalityIntegral_eq_zero_of_integrable (hπ₁ : IsAdmissible π₁)
    (hπ₂ : IsAdmissible π₂) (hi₁ : π₁.IsIrreducible) (hi₂ : π₂.IsIrreducible)
    (hne : IsEmpty (π₁.Equiv π₂)) (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂)
    (ℓ₂ : SmoothDual π₂) :
    orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ = 0 := by
  obtain ⟨T, hT⟩ :=
    exists_intertwiningMap_orthogonalityIntegral_left A μ h₁ h₂ hint hcof hπ₁ hπ₂ ℓ₁ v₂
  have := hi₁
  have := hi₂
  have := hne
  have hT0 : T = 0 := Subsingleton.elim _ _
  rw [← hT v₁ ℓ₂, hT0]
  exact map_zero _

end Forms

section SquareIntegrable

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V₁ : Type v} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type w} [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ G V₁} {π₂ : Representation ℂ G V₂} {χ : A →* ℂˣ}
  (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x)

/-- **Waldspurger III.1 (2)**: if the irreducible representations `π₁`, `π₂`, square integrable
modulo `A`, are not equivalent, then `I(v₁, ℓ₁, v₂, ℓ₂) = 0` for all `v₁, ℓ₁, v₂, ℓ₂`. -/
theorem orthogonalityIntegral_eq_zero
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hsq₁ : IsSquareIntegrableModCentralSubgroup A hA π₁ μ)
    (hsq₂ : IsSquareIntegrableModCentralSubgroup A hA π₂ μ)
    (hi₁ : π₁.IsIrreducible) (hi₂ : π₂.IsIrreducible)
    (hne : IsEmpty (π₁.Equiv π₂)) (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂)
    (ℓ₂ : SmoothDual π₂) :
    orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ = 0 :=
  orthogonalityIntegral_eq_zero_of_integrable A μ h₁ h₂
    (integrable_orthogonalityIntegrand A hA μ h₁ h₂ hsq₁ hsq₂) hcof hsq₁.1 hsq₂.1 hi₁ hi₂ hne
    v₁ ℓ₁ v₂ ℓ₂

end SquareIntegrable

section Unitary

variable {G : Type u} [Group G] (A : Subgroup G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {χ : A →* ℂˣ}

/-- `g ↦ ℓ(π(g) v) conj (ℓ(π(g) w))`, the integrand of the invariant Hermitian form of the
proof of Lemma III.1.3. -/
def formFun (π : Representation ℂ G V) (ℓ : Module.Dual ℂ V) (v w : V) (g : G) : ℂ :=
  ℓ (π g v) * conj (ℓ (π g w))

theorem formFun_mul (h : ∀ (a : A) (x : V), π a x = (χ a : ℂ) • x)
    (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1) (ℓ : Module.Dual ℂ V) (v w : V) (g : G) (a : A) :
    formFun π ℓ v w (g * (a : G)) = formFun π ℓ v w g := by
  unfold formFun
  have e : ∀ x : V, π (g * a) x = (χ a : ℂ) • π g x := fun x => by
    rw [map_mul, Module.End.mul_apply, h, map_smul]
  have hχ : (χ a : ℂ) * conj (χ a : ℂ) = 1 := by
    rw [Complex.mul_conj', hu]
    simp
  rw [e, e, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, mul_mul_mul_comm, hχ,
    one_mul]

/-- The integrand of the invariant form on `G/A`; it is well defined since `χ` is unitary. -/
def formIntegrand (h : ∀ (a : A) (x : V), π a x = (χ a : ℂ) • x)
    (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1) (ℓ : Module.Dual ℂ V) (v w : V) : G ⧸ A → ℂ :=
  Quotient.lift (formFun π ℓ v w) (by
    intro x y hxy
    have hz : x⁻¹ * y ∈ A := QuotientGroup.leftRel_apply.mp hxy
    have e := formFun_mul A h hu ℓ v w x ⟨x⁻¹ * y, hz⟩
    simpa using e.symm)

variable (h : ∀ (a : A) (x : V), π a x = (χ a : ℂ) • x) (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

@[simp]
theorem formIntegrand_mk (ℓ : Module.Dual ℂ V) (v w : V) (g : G) :
    formIntegrand A h hu ℓ v w (QuotientGroup.mk g) = ℓ (π g v) * conj (ℓ (π g w)) := rfl

theorem formIntegrand_swap (ℓ : Module.Dual ℂ V) (v w : V) (q : G ⧸ A) :
    formIntegrand A h hu ℓ w v q = conj (formIntegrand A h hu ℓ v w q) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ (π g w) * conj (ℓ (π g v)) = conj (ℓ (π g v) * conj (ℓ (π g w)))
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem formIntegrand_self_mk (ℓ : Module.Dual ℂ V) (v : V) (g : G) :
    formIntegrand A h hu ℓ v v (QuotientGroup.mk g) = ((‖ℓ (π g v)‖ ^ 2 : ℝ) : ℂ) := by
  change ℓ (π g v) * conj (ℓ (π g v)) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]

theorem formIntegrand_self (ℓ : Module.Dual ℂ V) (v : V) (q : G ⧸ A) :
    formIntegrand A h hu ℓ v v q = ((formIntegrand A h hu ℓ v v q).re : ℂ) ∧
      0 ≤ (formIntegrand A h hu ℓ v v q).re := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [formIntegrand_self_mk, Complex.ofReal_re]
  exact ⟨rfl, by positivity⟩

theorem formIntegrand_add_left (ℓ : Module.Dual ℂ V) (v v' w : V) :
    formIntegrand A h hu ℓ (v + v') w =
      formIntegrand A h hu ℓ v w + formIntegrand A h hu ℓ v' w := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ (π g (v + v')) * _ = ℓ (π g v) * _ + ℓ (π g v') * _
  rw [map_add, map_add, add_mul]

theorem formIntegrand_smul_left (ℓ : Module.Dual ℂ V) (c : ℂ) (v w : V) :
    formIntegrand A h hu ℓ (c • v) w = fun q => c * formIntegrand A h hu ℓ v w q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ (π g (c • v)) * _ = c * (ℓ (π g v) * _)
  rw [map_smul, map_smul, smul_eq_mul, mul_assoc]

theorem continuous_formIntegrand [TopologicalSpace G] [IsTopologicalGroup G] (hπ : IsSmooth π)
    (ℓ : Module.Dual ℂ V) (v w : V) : Continuous (formIntegrand A h hu ℓ v w) := by
  have c₁ : Continuous fun g : G => ℓ (π g v) :=
    (matrixCoefficient_isLocallyConstant π ℓ v (hπ v)).continuous
  have c₂ : Continuous fun g : G => ℓ (π g w) :=
    (matrixCoefficient_isLocallyConstant π ℓ w (hπ w)).continuous
  have c : Continuous (formFun π ℓ v w) := c₁.mul (Complex.continuous_conj.comp c₂)
  exact c.quotient_lift _

end Unitary

section FormalDegree

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {χ : A →* ℂˣ}
  (h : ∀ (a : A) (x : V), π a x = (χ a : ℂ) • x) (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

omit [IsTopologicalGroup G] [A.Normal] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)] in
/-- Smooth functionals separate points: a nonzero vector has a smooth functional with value
`1` on it. -/
theorem exists_smoothDual_eq_one [IsTopologicalGroup G]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hπ : IsSmooth π) {v : V} (hv : v ≠ 0) : ∃ ℓ : SmoothDual π, ℓ.val v = 1 := by
  obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal hcof π hπ hv
  refine ⟨(ℓ.val v)⁻¹ • ℓ, ?_⟩
  change (ℓ.val v)⁻¹ * ℓ.val v = 1
  exact inv_mul_cancel₀ hℓ

omit [μ.IsInvInvariant] in
/-- The integrand of the invariant form is integrable. -/
theorem integrable_formIntegrand (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (ℓ : SmoothDual π) (v w : V) : Integrable (formIntegrand A h hu ℓ.val v w) μ := by
  obtain ⟨hadm, c, hc⟩ := hsq
  have hint := (hc ℓ v).integrable_mul (hc ℓ w)
  refine hint.mono' ((continuous_formIntegrand A h hu hadm.1 ℓ.val v w).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ‖ℓ.val (π g v) * conj (ℓ.val (π g w))‖ ≤
    centralSubgroupCoefficientNorm A hA c ℓ v (QuotientGroup.mk g) *
      centralSubgroupCoefficientNorm A hA c ℓ w (QuotientGroup.mk g)
  rw [centralSubgroupCoefficientNorm_mk, centralSubgroupCoefficientNorm_mk, norm_mul,
    Complex.norm_conj]
  exact le_rfl

/-- The invariant Hermitian form `(v, w) = ∫_{G/A} ℓ(π(g) v) conj(ℓ(π(g) w)) dg` of the proof
of Lemma III.1.3, for a fixed smooth functional `ℓ`. -/
def invariantForm (ℓ : SmoothDual π) (v w : V) : ℂ :=
  ∫ q, formIntegrand A h hu ℓ.val v w q ∂μ

omit [μ.IsInvInvariant] in
theorem invariantForm_add_left (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (ℓ : SmoothDual π) (v v' w : V) :
    invariantForm A μ h hu ℓ (v + v') w =
      invariantForm A μ h hu ℓ v w + invariantForm A μ h hu ℓ v' w := by
  unfold invariantForm
  rw [formIntegrand_add_left]
  exact integral_add (integrable_formIntegrand A hA μ h hu hsq ℓ v w)
    (integrable_formIntegrand A hA μ h hu hsq ℓ v' w)

omit [IsTopologicalGroup G] [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure]
  [μ.IsInvInvariant] in
theorem invariantForm_smul_left (ℓ : SmoothDual π) (c : ℂ) (v w : V) :
    invariantForm A μ h hu ℓ (c • v) w = c * invariantForm A μ h hu ℓ v w := by
  unfold invariantForm
  rw [formIntegrand_smul_left, integral_const_mul]

omit [IsTopologicalGroup G] [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure]
  [μ.IsInvInvariant] in
/-- The form is Hermitian. -/
theorem invariantForm_swap (ℓ : SmoothDual π) (v w : V) :
    invariantForm A μ h hu ℓ w v = conj (invariantForm A μ h hu ℓ v w) := by
  unfold invariantForm
  simp_rw [formIntegrand_swap A h hu ℓ.val v w]
  exact integral_conj

/-- The form is `G`-invariant. -/
theorem invariantForm_rho (ℓ : SmoothDual π) (g : G) (v w : V) :
    invariantForm A μ h hu ℓ (π g v) (π g w) = invariantForm A μ h hu ℓ v w := by
  unfold invariantForm
  rw [← integral_mul_right_eq_self_of_inv (formIntegrand A h hu ℓ.val v w)
    (QuotientGroup.mk g : G ⧸ A)]
  congr 1
  funext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ.val (π x (π g v)) * conj (ℓ.val (π x (π g w))) =
    ℓ.val (π (x * g) v) * conj (ℓ.val (π (x * g) w))
  simp only [map_mul, Module.End.mul_apply]

omit [IsTopologicalGroup G] [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure]
  [μ.IsInvInvariant] in
/-- `(v, v)` is the integral of the nonnegative function `|ℓ(π(g) v)|²`. -/
theorem invariantForm_self (ℓ : SmoothDual π) (v : V) :
    invariantForm A μ h hu ℓ v v =
      ((∫ q, (formIntegrand A h hu ℓ.val v v q).re ∂μ : ℝ) : ℂ) := by
  unfold invariantForm
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  exact (formIntegrand_self A h hu ℓ.val v q).1

omit [μ.IsInvInvariant] in
/-- `(v, v) > 0` as soon as `ℓ(v) ≠ 0`. -/
theorem invariantForm_self_re_pos (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (ℓ : SmoothDual π) {v : V} (hv : ℓ.val v ≠ 0) :
    0 < ∫ q, (formIntegrand A h hu ℓ.val v v q).re ∂μ := by
  have hc : Continuous fun q => (formIntegrand A h hu ℓ.val v v q).re :=
    Complex.continuous_re.comp (continuous_formIntegrand A h hu hsq.1.1 ℓ.val v v)
  have hi : Integrable (fun q => (formIntegrand A h hu ℓ.val v v q).re) μ :=
    (integrable_formIntegrand A hA μ h hu hsq ℓ v v).re
  rw [integral_pos_iff_support_of_nonneg (fun q => (formIntegrand_self A h hu ℓ.val v q).2) hi]
  refine hc.isOpen_support.measure_pos μ ⟨QuotientGroup.mk 1, ?_⟩
  rw [Function.mem_support, formIntegrand_self_mk, Complex.ofReal_re, map_one,
    Module.End.one_apply]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

/-- **Unitarity** (proof of Lemma III.1.3, irreducible case): if `π` is irreducible and
`ℓ ≠ 0`, the invariant form is positive definite: `(v, v) > 0` for every `v ≠ 0`. -/
theorem invariantForm_self_re_pos_of_ne_zero
    (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ) (hi : π.IsIrreducible)
    (ℓ : SmoothDual π) {x₀ : V} (hx₀ : ℓ.val x₀ ≠ 0) {v : V} (hv : v ≠ 0) :
    0 < (invariantForm A μ h hu ℓ v v).re := by
  have hℓ : ℓ.val ≠ 0 := fun h0 => hx₀ (by rw [h0, LinearMap.zero_apply])
  obtain ⟨g, hg⟩ : ∃ g : G, ℓ.val (π g v) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hv (eq_zero_of_matrixCoefficient_vanishes π hi ℓ.val hℓ hall)
  rw [← invariantForm_rho A μ h hu ℓ g v v, invariantForm_self, Complex.ofReal_re]
  exact invariantForm_self_re_pos A hA μ h hu hsq ℓ hg

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ A)] [μ.IsInvInvariant] in
include h in
/-- The character `χ` by which an irreducible `π`, square integrable modulo `A`, acts on `A`
is unitary (it is the restriction of the unitary central character supplied by `hsq`). -/
theorem norm_character_eq_one (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) : ∀ a : A, ‖(χ a : ℂ)‖ = 1 := by
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨c, -⟩ := hsq.2
  intro a
  have e : (χ a : ℂ) • v₀ = (c.character ⟨a, hA a.2⟩ : ℂ) • v₀ := by
    rw [← h, ← c.acts]
  rw [smul_left_injective ℂ hv₀ e]
  exact c.norm_eq_one _

/-- The invariant form as a Library `InvariantPositiveForm`, with Mathlib's convention
(conjugate linear in the first argument): `⟪v, w⟫ = (w, v)`. It is positive definite when `π`
is irreducible and `ℓ ≠ 0`. -/
def invariantPositiveForm (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) (ℓ : SmoothDual π) {x₀ : V} (hx₀ : ℓ.val x₀ ≠ 0) :
    InvariantPositiveForm π where
  inner v w := invariantForm A μ h hu ℓ w v
  conj_inner_symm v w := (invariantForm_swap A μ h hu ℓ v w).symm
  re_inner_nonneg v := by
    show 0 ≤ (invariantForm A μ h hu ℓ v v).re
    rw [invariantForm_self, Complex.ofReal_re]
    exact integral_nonneg fun q => (formIntegrand_self A h hu ℓ.val v q).2
  add_left v w x := by
    show invariantForm A μ h hu ℓ x (v + w) =
      invariantForm A μ h hu ℓ x v + invariantForm A μ h hu ℓ x w
    rw [invariantForm_swap A μ h hu ℓ (v + w) x, invariantForm_add_left A hA μ h hu hsq ℓ v w x,
      map_add, ← invariantForm_swap, ← invariantForm_swap]
  smul_left v w c := by
    show invariantForm A μ h hu ℓ w (c • v) = conj c * invariantForm A μ h hu ℓ w v
    rw [invariantForm_swap A μ h hu ℓ (c • v) w, invariantForm_smul_left, map_mul,
      ← invariantForm_swap]
  definite v hv := by
    by_contra hne
    have hpos := invariantForm_self_re_pos_of_ne_zero A hA μ h hu hsq hi ℓ hx₀ hne
    change invariantForm A μ h hu ℓ v v = 0 at hv
    rw [hv, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  invariant g v w := invariantForm_rho A μ h hu ℓ g w v

theorem invariantPositiveForm_inner (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) (ℓ : SmoothDual π) {x₀ : V} (hx₀ : ℓ.val x₀ ≠ 0) (v w : V) :
    (invariantPositiveForm A hA μ h hu hsq hi ℓ hx₀).inner v w =
      invariantForm A μ h hu ℓ w v := rfl

include h in
/-- **Unitarity** (Lemma III.1.3, irreducible case): an irreducible representation that is
square integrable modulo `A` is unitarizable. -/
theorem isUnitarizable_of_isSquareIntegrable
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ) (hi : π.IsIrreducible) :
    IsUnitarizable π := by
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_smoothDual_eq_one hcof hsq.1.1 hv₀
  have hx₀ : ℓ₀.val v₀ ≠ 0 := by
    rw [hℓ₀]
    exact one_ne_zero
  exact ⟨invariantPositiveForm A hA μ h (norm_character_eq_one A hA μ h hsq hi) hsq hi ℓ₀ hx₀⟩

/-- The smooth functional `x ↦ (x, w)`. -/
def formFunctional (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ) (ℓ : SmoothDual π)
    (w : V) : SmoothDual π :=
  ⟨{ toFun := fun x => invariantForm A μ h hu ℓ x w
     map_add' := fun x y => invariantForm_add_left A hA μ h hu hsq ℓ x y w
     map_smul' := fun c x => by
       change invariantForm A μ h hu ℓ (c • x) w = c • invariantForm A μ h hu ℓ x w
       rw [smul_eq_mul]
       exact invariantForm_smul_left A μ h hu ℓ c x w }, by
    obtain ⟨K, hK⟩ := hsq.1.1 w
    refine ⟨K, fun k => ?_⟩
    apply LinearMap.ext
    intro x
    change invariantForm A μ h hu ℓ (π (k : G)⁻¹ x) w = invariantForm A μ h hu ℓ x w
    have hkw : π (k : G)⁻¹ w = w := hK k⁻¹
    conv_lhs => rw [← hkw]
    exact invariantForm_rho A μ h hu ℓ (k : G)⁻¹ x w⟩

theorem formFunctional_apply (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (ℓ : SmoothDual π) (w x : V) :
    (formFunctional A hA μ h hu hsq ℓ w).val x = invariantForm A μ h hu ℓ x w := rfl

variable (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hcof in
/-- For an irreducible `π`, `I(v₁, ℓ₁, v₂, ℓ₂) = κ ℓ₂(v₁) ℓ₁(v₂)` for a complex constant `κ`
(the Schur step of III.1 (3)). -/
theorem exists_orthogonalityIntegral_eq_mul
    (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ) (hi : π.IsIrreducible) :
    ∃ κ : ℂ, ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = κ * ℓ₂.val v₁ * ℓ₁.val v₂ := by
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_smoothDual_eq_one hcof hsq.1.1 hv₀
  have hL : ∀ (ℓ₁ : SmoothDual π) (v₂ : V), ∃ c : ℂ, ∀ (v₁ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = c * ℓ₂.val v₁ := by
    intro ℓ₁ v₂
    obtain ⟨T, hT⟩ :=
      exists_intertwiningMap_orthogonalityIntegral_left A μ h h
        (integrable_orthogonalityIntegrand A hA μ h h hsq hsq) hcof hsq.1 hsq.1 ℓ₁ v₂
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism π hsq.1 hi T
    refine ⟨c, fun v₁ ℓ₂ => ?_⟩
    rw [← hT, hc]
    change ℓ₂.val (c • v₁) = c * ℓ₂.val v₁
    rw [map_smul, smul_eq_mul]
  have hR : ∀ (v₁ : V) (ℓ₂ : SmoothDual π), ∃ c : ℂ, ∀ (v₂ : V) (ℓ₁ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = c * ℓ₁.val v₂ := by
    intro v₁ ℓ₂
    obtain ⟨T, hT⟩ :=
      exists_intertwiningMap_orthogonalityIntegral_right A μ h h
        (integrable_orthogonalityIntegrand A hA μ h h hsq hsq) hcof hsq.1 hsq.1 v₁ ℓ₂
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism π hsq.1 hi T
    refine ⟨c, fun v₂ ℓ₁ => ?_⟩
    rw [← hT, hc]
    change ℓ₁.val (c • v₂) = c * ℓ₁.val v₂
    rw [map_smul, smul_eq_mul]
  obtain ⟨κ, hκ⟩ := hR v₀ ℓ₀
  refine ⟨κ, fun v₁ ℓ₁ v₂ ℓ₂ => ?_⟩
  obtain ⟨c, hc⟩ := hL ℓ₁ v₂
  have e : c = κ * ℓ₁.val v₂ := by
    have e₁ := hc v₀ ℓ₀
    rw [hℓ₀, mul_one] at e₁
    rw [← e₁, hκ]
  rw [hc, e]
  ring

include hcof in
/-- **Waldspurger III.1 (3)**: for an irreducible `π`, square integrable modulo `A`, there is a
real `d > 0` (the formal degree) with `I(v₁, ℓ₁, v₂, ℓ₂) = d⁻¹ ℓ₂(v₁) ℓ₁(v₂)`, i.e.
`d⁻¹ ⟨v₁, ℓ₂⟩ ⟨v₂, ℓ₁⟩`. -/
theorem exists_formalDegree (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) :
    ∃ d : ℝ, 0 < d ∧ ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = (d : ℂ)⁻¹ * ℓ₂.val v₁ * ℓ₁.val v₂ := by
  obtain ⟨κ, hκ⟩ := exists_orthogonalityIntegral_eq_mul A hA μ h hcof hsq hi
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_smoothDual_eq_one hcof hsq.1.1 hv₀
  have hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1 := norm_character_eq_one A hA μ h hsq hi
  have hr := invariantForm_self_re_pos A hA μ h hu hsq ℓ₀ (v := v₀)
    (by rw [hℓ₀]; exact one_ne_zero)
  set r := ∫ q, (formIntegrand A h hu ℓ₀.val v₀ v₀ q).re ∂μ with hr_def
  have hHv : invariantForm A μ h hu ℓ₀ v₀ v₀ = (r : ℂ) := invariantForm_self A μ h hu ℓ₀ v₀
  set ℓv := formFunctional A hA μ h hu hsq ℓ₀ v₀ with hℓv
  have hF : ∀ g : G, orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val (QuotientGroup.mk g) =
      ((‖invariantForm A μ h hu ℓ₀ (π g v₀) v₀‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    change invariantForm A μ h hu ℓ₀ (π g v₀) v₀ * invariantForm A μ h hu ℓ₀ (π g⁻¹ v₀) v₀ = _
    have e : invariantForm A μ h hu ℓ₀ (π g⁻¹ v₀) v₀ =
        conj (invariantForm A μ h hu ℓ₀ (π g v₀) v₀) := by
      rw [← invariantForm_rho A μ h hu ℓ₀ g (π g⁻¹ v₀) v₀, Representation.self_inv_apply,
        invariantForm_swap]
    rw [e, Complex.mul_conj', Complex.ofReal_pow]
  have hFre : ∀ q, orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val q =
      ((orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val q).re : ℂ) ∧
        0 ≤ (orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val q).re := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hF, Complex.ofReal_re]
    exact ⟨rfl, by positivity⟩
  set s := ∫ q, (orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val q).re ∂μ with hs_def
  have hI : orthogonalityIntegral A μ h h v₀ ℓv v₀ ℓv = (s : ℂ) := by
    unfold orthogonalityIntegral
    rw [← integral_complex_ofReal]
    congr 1
    funext q
    exact (hFre q).1
  have hs : 0 < s := by
    have hc : Continuous fun q => (orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val q).re :=
      Complex.continuous_re.comp
        (continuous_orthogonalityIntegrand A h h hsq.1.1 hsq.1.1 v₀ ℓv.val v₀ ℓv.val)
    have hint : Integrable
        (fun q => (orthogonalityIntegrand A h h v₀ ℓv.val v₀ ℓv.val q).re) μ :=
      (integrable_orthogonalityIntegrand A hA μ h h hsq hsq v₀ ℓv v₀ ℓv).re
    rw [hs_def, integral_pos_iff_support_of_nonneg (fun q => (hFre q).2) hint]
    refine hc.isOpen_support.measure_pos μ ⟨QuotientGroup.mk 1, ?_⟩
    rw [Function.mem_support, hF, Complex.ofReal_re, map_one, Module.End.one_apply, hHv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    positivity
  have hκr : κ * (r : ℂ) * (r : ℂ) = (s : ℂ) := by
    rw [← hI, hκ, formFunctional_apply, hHv]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hκ' : κ = (s : ℂ) / (r : ℂ) ^ 2 :=
    eq_div_of_mul_eq (pow_ne_zero 2 hr0) (by rw [← hκr]; ring)
  refine ⟨r ^ 2 / s, by positivity, fun v₁ ℓ₁ v₂ ℓ₂ => ?_⟩
  rw [hκ, hκ']
  push_cast
  rw [inv_div]

omit [BorelSpace (G ⧸ A)] [μ.IsInvInvariant] in
include hcof in
/-- The formal degree is unique. -/
theorem formalDegree_unique (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) {d d' : ℝ}
    (hd : ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = (d : ℂ)⁻¹ * ℓ₂.val v₁ * ℓ₁.val v₂)
    (hd' : ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = (d' : ℂ)⁻¹ * ℓ₂.val v₁ * ℓ₁.val v₂) :
    d = d' := by
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_smoothDual_eq_one hcof hsq.1.1 hv₀
  have e := (hd v₀ ℓ₀ v₀ ℓ₀).symm.trans (hd' v₀ ℓ₀ v₀ ℓ₀)
  simp only [hℓ₀, mul_one, inv_inj] at e
  exact_mod_cast e

/-- The formal degree `d(π)` of Waldspurger III.1 (3) (for the Haar measure `μ` on `G/A`). -/
def formalDegree (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) : ℝ :=
  Classical.choose (exists_formalDegree A hA μ h hcof hsq hi)

theorem formalDegree_pos (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ)
    (hi : π.IsIrreducible) : 0 < formalDegree A hA μ h hcof hsq hi :=
  (Classical.choose_spec (exists_formalDegree A hA μ h hcof hsq hi)).1

/-- `I(v₁, ℓ₁, v₂, ℓ₂) = d(π)⁻¹ ⟨v₁, ℓ₂⟩ ⟨v₂, ℓ₁⟩`. -/
theorem orthogonalityIntegral_eq_formalDegree
    (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ) (hi : π.IsIrreducible)
    (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π) :
    orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ =
      (formalDegree A hA μ h hcof hsq hi : ℂ)⁻¹ * ℓ₂.val v₁ * ℓ₁.val v₂ :=
  (Classical.choose_spec (exists_formalDegree A hA μ h hcof hsq hi)).2 v₁ ℓ₁ v₂ ℓ₂

end FormalDegree

end Langlands.HarishChandraSchwartz
