import Langlands.Representation.Compact.SquareIntegrableUnitarySemisimpleProof
import Langlands.Representation.Compact.EssentiallySquareIntegrableAdmissibleProof
import Langlands.Representation.Unitary.AdmissibleFormUniqueness
import Langlands.Representation.Plancherel.FormalDegreeComparisons

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.Renard.CompactRepresentation

open Langlands.HarishChandraSchwartz Langlands.Plancherel

universe u v w

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V₁ : Type v} [AddCommGroup V₁] [Module ℂ V₁]
  {V₂ : Type w} [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ G V₁} {π₂ : Representation ℂ G V₂} {χ : A →* ℂˣ}
  (h₁ : ∀ (a : A) (x : V₁), π₁ a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : V₂), π₂ a x = (χ a : ℂ) • x)
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

omit [μ.IsMulRightInvariant] in
include hcof in
/-- An invariant positive form turns an inverse coefficient into the conjugate of a
forward coefficient, so only the supplied Haar and right invariance are used. -/
theorem integrable_orthogonality_of_positiveForm
    (hsq₁ : IsSquareIntegrableModCentralSubgroup A hA π₁ μ)
    (hsq₂ : IsSquareIntegrableModCentralSubgroup A hA π₂ μ)
    (b₂ : InvariantPositiveForm π₂)
    (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) (ℓ₂ : SmoothDual π₂) :
    Integrable (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ ℓ₂.val) μ := by
  obtain ⟨z, rfl⟩ := b₂.toSmoothDual_surjective hcof hsq₂.1 ℓ₂
  obtain ⟨c₁, hc₁⟩ := hsq₁.2
  obtain ⟨c₂, hc₂⟩ := hsq₂.2
  have hint := (hc₁ ℓ₁ v₁).integrable_mul (hc₂ (b₂.toSmoothDual hsq₂.1.1 v₂) z)
  refine hint.mono'
    (continuous_orthogonalityIntegrand A h₁ h₂ hsq₁.1.1 hsq₂.1.1 v₁ ℓ₁.val v₂
      (b₂.toSmoothDual hsq₂.1.1 z).val).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have he : b₂.inner z (π₂ g⁻¹ v₂) = conj (b₂.inner v₂ (π₂ g z)) := by
    rw [← b₂.invariant g z (π₂ g⁻¹ v₂), Representation.self_inv_apply]
    exact (b₂.conj_inner_symm _ _).symm
  change ‖ℓ₁.val (π₁ g v₁) * b₂.inner z (π₂ g⁻¹ v₂)‖ ≤
    centralSubgroupCoefficientNorm A hA c₁ ℓ₁ v₁ (QuotientGroup.mk g) *
      centralSubgroupCoefficientNorm A hA c₂ (b₂.toSmoothDual hsq₂.1.1 v₂) z
        (QuotientGroup.mk g)
  rw [centralSubgroupCoefficientNorm_mk, centralSubgroupCoefficientNorm_mk, he, norm_mul,
    Complex.norm_conj]
  exact le_rfl

omit [μ.IsHaarMeasure] in
/-- Right invariance gives the first Schur invariance directly. -/
theorem orthogonalityIntegral_rho_left_rightInvariant (g : G) (v₁ : V₁)
    (ℓ₁ : SmoothDual π₁) (v₂ : V₂) (ℓ₂ : SmoothDual π₂) :
    orthogonalityIntegral A μ h₁ h₂ (π₁ g v₁) ℓ₁ v₂ ℓ₂ =
      orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ (smoothContragredient π₂ g⁻¹ ℓ₂) := by
  unfold orthogonalityIntegral
  rw [← integral_mul_right_eq_self
    (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ (smoothContragredient π₂ g⁻¹ ℓ₂).val)
    (QuotientGroup.mk g : G ⧸ A)]
  congr 1
  funext q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁.val (π₁ a (π₁ g v₁)) * ℓ₂.val (π₂ a⁻¹ v₂) =
    ℓ₁.val (π₁ (a * g) v₁) * ℓ₂.val (π₂ g⁻¹⁻¹ (π₂ (a * g)⁻¹ v₂))
  simp only [map_mul, Module.End.mul_apply, mul_inv_rev, inv_inv,
    Representation.self_inv_apply]

omit [μ.IsHaarMeasure] in
include hcof in
/-- The left weak Schur form is represented by an actual intertwiner. -/
theorem exists_leftSchurIntertwiner_rightInvariant
    (hint : ∀ (v₁ : V₁) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) (ℓ₂ : SmoothDual π₂),
      Integrable (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ ℓ₂.val) μ)
    (hπ₁ : IsAdmissible π₁) (hπ₂ : IsAdmissible π₂) (ℓ₁ : SmoothDual π₁) (v₂ : V₂) :
    ∃ T : π₁.IntertwiningMap π₂, ∀ (v₁ : V₁) (ℓ₂ : SmoothDual π₂),
      smoothDualPairing π₂ ℓ₂ (T v₁) = orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ :=
  exists_intertwiningMap_of_weakForm_of_compact_cofinal hcof hπ₁.1 hπ₂
    (orthogonalityFormLeft A μ h₁ h₂ hint ℓ₁ v₂)
    (fun g y ℓ => orthogonalityIntegral_rho_left_rightInvariant A μ h₁ h₂ g y ℓ₁ v₂ ℓ)

end General

section Self

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {χ : A →* ℂˣ}
  (h : ∀ (a : A) (x : V), π a x = (χ a : ℂ) • x)
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hcof in
/-- Both Schur scalarizations with the given right invariant measure. -/
theorem exists_schurScalar_rightInvariant
    (hadm : IsAdmissible π) (hi : π.IsIrreducible)
    (hint : ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      Integrable (orthogonalityIntegrand A h h v₁ ℓ₁.val v₂ ℓ₂.val) μ) :
    ∃ κ : ℂ, ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = κ * ℓ₂.val v₁ * ℓ₁.val v₂ := by
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_smoothDual_eq_one hcof hadm.1 hv₀
  have hL : ∀ (ℓ₁ : SmoothDual π) (v₂ : V), ∃ c : ℂ, ∀ (v₁ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = c * ℓ₂.val v₁ := by
    intro ℓ₁ v₂
    obtain ⟨T, hT⟩ := exists_leftSchurIntertwiner_rightInvariant A μ h h hcof hint hadm hadm ℓ₁ v₂
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism π hadm hi T
    refine ⟨c, fun v₁ ℓ₂ => ?_⟩
    rw [← hT, hc]
    change ℓ₂.val (c • v₁) = c * ℓ₂.val v₁
    rw [map_smul, smul_eq_mul]
  have hR : ∀ (v₁ : V) (ℓ₂ : SmoothDual π), ∃ c : ℂ, ∀ (v₂ : V) (ℓ₁ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = c * ℓ₁.val v₂ := by
    intro v₁ ℓ₂
    obtain ⟨T, hT⟩ := exists_intertwiningMap_orthogonalityIntegral_right A μ h h
      hint hcof hadm hadm v₁ ℓ₂
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism π hadm hi T
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
/-- The Schur scalar is positive real, using a diagonal coefficient of the positive form. -/
theorem exists_formalDegree_rightInvariant
    (hsq : IsSquareIntegrableModCentralSubgroup A hA π μ) (hi : π.IsIrreducible)
    (b : InvariantPositiveForm π) :
    ∃ d : ℝ, 0 < d ∧ ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : V) (ℓ₂ : SmoothDual π),
      orthogonalityIntegral A μ h h v₁ ℓ₁ v₂ ℓ₂ = (d : ℂ)⁻¹ * ℓ₂.val v₁ * ℓ₁.val v₂ := by
  have hint := integrable_orthogonality_of_positiveForm A hA μ h h hcof hsq hsq b
  obtain ⟨κ, hκ⟩ := exists_schurScalar_rightInvariant A μ h hcof hsq.1 hi hint
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ℓ := b.toSmoothDual hsq.1.1 v
  let r := (b.inner v v).re
  have hr : 0 < r := b.inner_self_re_pos hv
  have hrv : ℓ.val v = (r : ℂ) := (b.inner_self_ofReal_re v).symm
  have hF (g : G) : orthogonalityIntegrand A h h v ℓ.val v ℓ.val (QuotientGroup.mk g) =
      ((‖ℓ.val (π g v)‖ ^ 2 : ℝ) : ℂ) := by
    change b.inner v (π g v) * b.inner v (π g⁻¹ v) = _
    have he : b.inner v (π g⁻¹ v) = conj (b.inner v (π g v)) := by
      rw [← b.invariant g v (π g⁻¹ v), Representation.self_inv_apply]
      exact (b.conj_inner_symm _ _).symm
    rw [he, Complex.mul_conj', Complex.ofReal_pow]
    rfl
  have hFre (q : G ⧸ A) : orthogonalityIntegrand A h h v ℓ.val v ℓ.val q =
      ((orthogonalityIntegrand A h h v ℓ.val v ℓ.val q).re : ℂ) ∧
      0 ≤ (orthogonalityIntegrand A h h v ℓ.val v ℓ.val q).re := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hF, Complex.ofReal_re]
    exact ⟨rfl, by positivity⟩
  let s := ∫ q, (orthogonalityIntegrand A h h v ℓ.val v ℓ.val q).re ∂μ
  have hs : 0 < s := by
    have hc := Complex.continuous_re.comp
      (continuous_orthogonalityIntegrand A h h hsq.1.1 hsq.1.1 v ℓ.val v ℓ.val)
    change 0 < ∫ q, (orthogonalityIntegrand A h h v ℓ.val v ℓ.val q).re ∂μ
    rw [integral_pos_iff_support_of_nonneg (fun q => (hFre q).2) (hint v ℓ v ℓ).re]
    refine hc.isOpen_support.measure_pos μ ⟨QuotientGroup.mk 1, ?_⟩
    rw [Function.mem_support, Function.comp_apply, hF, map_one, Module.End.one_apply, hrv, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    positivity
  have hI : orthogonalityIntegral A μ h h v ℓ v ℓ = (s : ℂ) := by
    unfold orthogonalityIntegral s
    rw [← integral_complex_ofReal]
    congr 1
    funext q
    exact (hFre q).1
  have hκr : κ * (r : ℂ) * (r : ℂ) = (s : ℂ) := by
    rw [← hI, hκ, hrv]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hκ' : κ = (s : ℂ) / (r : ℂ) ^ 2 :=
    eq_div_of_mul_eq (pow_ne_zero 2 hr0) (by rw [← hκr]; ring)
  refine ⟨r ^ 2 / s, by positivity, fun v₁ ℓ₁ v₂ ℓ₂ => ?_⟩
  rw [hκ, hκ']
  push_cast
  rw [inv_div]

end Self

section FullCenter

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

/-- The exact self relation in Renard IV.3.3, including integrability and positive degree. -/
theorem schurOrthogonality_self (π : SmoothRep.{0, u, v} ℂ G) (hi : π.IsIrreducible)
    (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G))
    (c : UnitaryCentralCharacter (π.twist ω hω).representation)
    (hc : ∀ (ℓ : SmoothDual (π.twist ω hω).representation) (x : π),
      MemLp (c.coefficientNorm ℓ x) 2 μ) :
    ∃ d : ℝ, 0 < d ∧
      ∀ (x₁ x₂ : π) (ℓ₁ ℓ₂ : SmoothDual π.representation)
        (F : G ⧸ Subgroup.center G → ℂ),
        (∀ g : G, F (QuotientGroup.mk g) =
          (ℓ₁ : Module.Dual ℂ π) (π.representation g x₁) *
            (ℓ₂ : Module.Dual ℂ π) (π.representation g⁻¹ x₂)) →
        Integrable F μ ∧
          ∫ q, F q ∂μ = (ℓ₁ : Module.Dual ℂ π) x₂ * (ℓ₂ : Module.Dual ℂ π) x₁ / d := by
  have hadm : π.IsAdmissible := essentiallySquareIntegrableAdmissible G μ π hi ω hω ⟨c, hc⟩
  have hadmt : (π.twist ω hω).IsAdmissible := (π.isAdmissible_twist_iff ω hω).mpr hadm
  have hsq : IsSquareIntegrableModCenter (π.twist ω hω).representation μ := ⟨hadmt, c, hc⟩
  have hit : (π.twist ω hω).IsIrreducible := (π.isIrreducible_twist_iff ω hω).mpr hi
  obtain ⟨b⟩ := (squareIntegrableUnitarySemisimple G μ (π.twist ω hω) hsq).1
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one
  have hsqA := (squareIntegrableModCenter_iff_fullCenter μ).mp hsq
  obtain ⟨d, hd, hdeg⟩ := exists_formalDegree_rightInvariant (Subgroup.center G)
    le_rfl μ c.acts hcof hsqA hit b
  refine ⟨d, hd, fun x₁ x₂ ℓ₁ ℓ₂ F hF => ?_⟩
  let ℓ₁t : SmoothDual (π.twist ω hω).representation :=
    (smoothContragredientTwistEquiv ω π.representation hω).symm ℓ₁
  let ℓ₂t : SmoothDual (π.twist ω hω).representation :=
    (smoothContragredientTwistEquiv ω π.representation hω).symm ℓ₂
  have he : F = orthogonalityIntegrand (Subgroup.center G) c.acts c.acts
      x₁ ℓ₁t.val x₂ ℓ₂t.val := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hF]
    change ℓ₁.val (π.representation g x₁) * ℓ₂.val (π.representation g⁻¹ x₂) =
      ℓ₁.val ((ω g : ℂ) • π.representation g x₁) *
        ℓ₂.val ((ω g⁻¹ : ℂ) • π.representation g⁻¹ x₂)
    simp only [map_smul, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val]
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  refine ⟨he ▸ integrable_orthogonality_of_positiveForm (Subgroup.center G)
    le_rfl μ c.acts c.acts hcof hsqA hsqA b x₁ ℓ₁t x₂ ℓ₂t, ?_⟩
  rw [he]
  change orthogonalityIntegral (Subgroup.center G) μ c.acts c.acts x₁ ℓ₁t x₂ ℓ₂t = _
  rw [hdeg]
  change (d : ℂ)⁻¹ * ℓ₂.val x₁ * ℓ₁.val x₂ = _
  rw [div_eq_mul_inv]
  ring

end FullCenter

end Langlands.Renard.CompactRepresentation
