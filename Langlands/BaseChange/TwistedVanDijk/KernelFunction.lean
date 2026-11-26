import Langlands.BaseChange.TwistedVanDijk.Measures
import Langlands.Representation.Induction.CompactQuotientDuality

/-! # The kernel functions of the twisted van Dijk formula

For a test function `φ` on `G = GL_n(E)` and `g, y ∈ G`, the function
`m ↦ δ_P(m)^{1/2} ∫_U φ(g⁻¹ σ(m u y)) du` on the Levi `M` is a test function. Composing its
integrated Levi action on the left with the tensor intertwiner `A₁ ⊗ ⋯ ⊗ A_r` gives the
operator-valued kernel of `π(φ) ∘ ι(A)` in the compact model. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory Measure GeneralLinear HarmonicAnalysis
open scoped ENNReal NNReal

universe u v

section Conjugation

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
theorem leviEmbedding_conj_mem_unipotentSubgroup' (a : B.Levi E) {y : GeneralLinear n E}
    (hy : y ∈ B.unipotentSubgroup E) :
    B.leviEmbedding E a * y * (B.leviEmbedding E a)⁻¹ ∈ B.unipotentSubgroup E := by
  have := leviEmbedding_conj_mem_unipotentSubgroup B a⁻¹ hy
  rwa [map_inv, inv_inv] at this

/-- Conjugation `y ↦ m y m⁻¹` of the unipotent radical by a block diagonal element. -/
def unipotentConj (a : B.Levi E) : B.unipotentSubgroup E ≃ₜ* B.unipotentSubgroup E where
  toFun y := ⟨B.leviEmbedding E a * y * (B.leviEmbedding E a)⁻¹,
    leviEmbedding_conj_mem_unipotentSubgroup' B a y.property⟩
  invFun y := ⟨(B.leviEmbedding E a)⁻¹ * y * B.leviEmbedding E a,
    leviEmbedding_conj_mem_unipotentSubgroup B a y.property⟩
  left_inv y := by
    apply Subtype.ext
    change (B.leviEmbedding E a)⁻¹ * (B.leviEmbedding E a * (y : GeneralLinear n E) *
      (B.leviEmbedding E a)⁻¹) * B.leviEmbedding E a = y
    group
  right_inv y := by
    apply Subtype.ext
    change B.leviEmbedding E a * ((B.leviEmbedding E a)⁻¹ * (y : GeneralLinear n E) *
      B.leviEmbedding E a) * (B.leviEmbedding E a)⁻¹ = y
    group
  map_mul' y z := by
    apply Subtype.ext
    change B.leviEmbedding E a * ((y : GeneralLinear n E) * z) * (B.leviEmbedding E a)⁻¹ =
      (B.leviEmbedding E a * y * (B.leviEmbedding E a)⁻¹) *
        (B.leviEmbedding E a * z * (B.leviEmbedding E a)⁻¹)
    group
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp]
theorem coe_unipotentConj (a : B.Levi E) (y : B.unipotentSubgroup E) :
    (unipotentConj B a y : GeneralLinear n E) =
      B.leviEmbedding E a * y * (B.leviEmbedding E a)⁻¹ := rfl

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact

/-- Haar measure on the unipotent radical is invariant under conjugation by an integral block
diagonal element. -/
theorem map_unipotentConj_eq [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] (μ : Measure (B.unipotentSubgroup E)) [μ.IsHaarMeasure]
    {a : B.Levi E} (ha : B.leviEmbedding E a ∈ integralGL E n) :
    μ.map (unipotentConj B a) = μ := by
  have hcl : IsClosed (B.unipotentSubgroup E : Set (GeneralLinear n E)) :=
    B.isClosed_unipotentSubgroup E
  refine map_eq_self_of_preimage_eq μ _
    (C := {y : B.unipotentSubgroup E | (y : GeneralLinear n E) ∈ integralGL E n})
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_integralGL n))
    ((isOpen_integralGL n).preimage continuous_subtype_val) ⟨1, (integralGL E n).one_mem⟩ ?_
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, coe_unipotentConj]
  constructor
  · intro h
    have := (integralGL E n).mul_mem ((integralGL E n).mul_mem ((integralGL E n).inv_mem ha) h) ha
    simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using this
  · intro h
    exact (integralGL E n).mul_mem ((integralGL E n).mul_mem ha h) ((integralGL E n).inv_mem ha)

end Conjugation

section Kernel

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  (μU : Measure (B.unipotentSubgroup E))

/-- The kernel value `δ_P(m)^{1/2} ∫_U φ(g⁻¹ σ(m u y)) du`. -/
def kernelValue (φ : GeneralLinear n E → ℂ) (g y : GeneralLinear n E) (m : B.Levi E) : ℂ :=
  ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
    ∫ u, φ (g⁻¹ * entrywiseAut σ n (B.leviEmbedding E m * (u : GeneralLinear n E) * y)) ∂μU

omit [TopologicalSpace F] [IsModuleTopology F E] [BorelSpace (GeneralLinear n E)] in
/-- Left invariance of `φ` under `K'` gives right invariance of the kernel in `g`. -/
theorem kernelValue_mul_right_left {φ : GeneralLinear n E → ℂ} {K' : Subgroup (GeneralLinear n E)}
    (hφ : ∀ k ∈ K', ∀ x, φ (k * x) = φ x) (g y : GeneralLinear n E) {k : GeneralLinear n E}
    (hk : k ∈ K') (m : B.Levi E) :
    kernelValue σ B μU φ (g * k) y m = kernelValue σ B μU φ g y m := by
  simp only [kernelValue, mul_inv_rev, mul_assoc]
  congr 2
  funext u
  exact hφ k⁻¹ (K'.inv_mem hk) _

omit [TopologicalSpace F] [IsModuleTopology F E] [BorelSpace (GeneralLinear n E)] in
/-- Right invariance of `φ` under a `σ`-stable `K'` gives right invariance of the kernel in
`y`. -/
theorem kernelValue_mul_right_right {φ : GeneralLinear n E → ℂ}
    {K' : Subgroup (GeneralLinear n E)} (hφ : ∀ k ∈ K', ∀ x, φ (x * k) = φ x)
    (hσ : ∀ k ∈ K', entrywiseAut σ n k ∈ K') (g y : GeneralLinear n E) {k : GeneralLinear n E}
    (hk : k ∈ K') (m : B.Levi E) :
    kernelValue σ B μU φ g (y * k) m = kernelValue σ B μU φ g y m := by
  simp only [kernelValue]
  congr 2
  funext u
  rw [← mul_assoc, map_mul, ← mul_assoc]
  exact hφ _ (hσ k hk) _

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact

/-- The open subgroup of `M` under whose right translations the kernel value at `(g, y)` is
invariant, for `φ` right invariant under `K''`. -/
def kernelStabilizer (K'' : Subgroup (GeneralLinear n E)) (y : GeneralLinear n E) :
    Subgroup (B.Levi E) :=
  (integralGL E n).comap (B.leviEmbedding E) ⊓
    (K''.comap ((entrywiseAut σ n).toMonoidHom.comp ((MulAut.conj y⁻¹).toMonoidHom.comp
      (B.leviEmbedding E)))) ⊓
    ((LocalFieldData.ofInstances E).leviHalfModulus B).ker

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)] in
theorem isOpen_kernelStabilizer {K'' : Subgroup (GeneralLinear n E)}
    (hK'' : IsOpen (K'' : Set (GeneralLinear n E))) (y : GeneralLinear n E) :
    IsOpen (kernelStabilizer σ B K'' y : Set (B.Levi E)) := by
  have hL : Continuous (B.leviEmbedding E) := (B.leviEmbeddingContinuous E).continuous
  refine ((((isOpen_integralGL n).preimage hL).inter ?_).inter ?_)
  · exact hK''.preimage ((continuous_entrywiseAut σ n).comp
      ((continuous_const.mul hL).mul continuous_const))
  · exact (LocalFieldData.ofInstances E).isOpen_ker_leviHalfModulus B

omit [TopologicalSpace F] [IsModuleTopology F E] in
/-- The kernel value is invariant under right translation by the kernel stabilizer. -/
theorem kernelValue_mul_stabilizer (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
    {φ : GeneralLinear n E → ℂ} {K'' : Subgroup (GeneralLinear n E)}
    (hφ : ∀ x, ∀ k ∈ K'', φ (x * k) = φ x) (g y : GeneralLinear n E) (m : B.Levi E)
    {m₀ : B.Levi E} (hm₀ : m₀ ∈ kernelStabilizer σ B K'' y) :
    kernelValue σ B μU φ g y (m * m₀) = kernelValue σ B μU φ g y m := by
  obtain ⟨⟨hK, hK''⟩, hδ⟩ := hm₀
  have hδ' : (LocalFieldData.ofInstances E).leviHalfModulus B m₀ = 1 := hδ
  have hint : (∫ u, φ (g⁻¹ * entrywiseAut σ n
        (B.leviEmbedding E (m * m₀) * (u : GeneralLinear n E) * y)) ∂μU) =
      ∫ u, φ (g⁻¹ * entrywiseAut σ n
        (B.leviEmbedding E m * (u : GeneralLinear n E) * y)) ∂μU := by
    have hpt : ∀ u : B.unipotentSubgroup E, φ (g⁻¹ * entrywiseAut σ n
        (B.leviEmbedding E (m * m₀) * (u : GeneralLinear n E) * y)) =
        φ (g⁻¹ * entrywiseAut σ n (B.leviEmbedding E m *
          (unipotentConj B m₀ u : GeneralLinear n E) * y)) := by
      intro u
      have hk : entrywiseAut σ n (y⁻¹ * B.leviEmbedding E m₀ * y) ∈ K'' := hK''
      have heq : B.leviEmbedding E (m * m₀) * (u : GeneralLinear n E) * y =
          (B.leviEmbedding E m * (unipotentConj B m₀ u : GeneralLinear n E) * y) *
            (y⁻¹ * B.leviEmbedding E m₀ * y) := by
        rw [coe_unipotentConj, map_mul]
        group
      rw [heq, map_mul, ← mul_assoc, hφ _ _ hk]
    simp_rw [hpt]
    have hmeas : MeasurableEmbedding (unipotentConj B m₀) :=
      (unipotentConj B m₀).toHomeomorph.isClosedEmbedding.measurableEmbedding
    rw [← hmeas.integral_map (fun v : B.unipotentSubgroup E => φ (g⁻¹ * entrywiseAut σ n
      (B.leviEmbedding E m * (v : GeneralLinear n E) * y))), map_unipotentConj_eq B μU hK]
  unfold kernelValue
  rw [hint, map_mul, Units.val_mul, hδ', Units.val_one, mul_one]

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)] in
/-- The kernel value is locally constant. -/
theorem isLocallyConstant_kernelValue [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
    {φ : GeneralLinear n E → ℂ} {K'' : Subgroup (GeneralLinear n E)}
    (hK'' : IsOpen (K'' : Set (GeneralLinear n E)))
    (hφ : ∀ x, ∀ k ∈ K'', φ (x * k) = φ x) (g y : GeneralLinear n E) :
    IsLocallyConstant (kernelValue σ B μU φ g y) :=
  Induction.isLocallyConstant_of_mul_right (kernelStabilizer σ B K'' y)
    (isOpen_kernelStabilizer σ B hK'' y) _
    (fun m _ hm₀ => kernelValue_mul_stabilizer σ B μU hφ g y m hm₀)

omit [BorelSpace (GeneralLinear n E)] in
/-- The kernel value vanishes outside a compact set when `φ` has compact support. -/
theorem hasCompactSupport_kernelValue (μU : Measure (B.unipotentSubgroup E))
    {φ : GeneralLinear n E → ℂ} (hφ : HasCompactSupport φ) (g y : GeneralLinear n E) :
    HasCompactSupport (kernelValue σ B μU φ g y) := by
  let θ : GeneralLinear n E → GeneralLinear n E := fun x => g⁻¹ * entrywiseAut σ n (x * y)
  have hθ : Continuous θ :=
    continuous_const.mul ((continuous_entrywiseAut σ n).comp (continuous_id.mul continuous_const))
  -- `θ` is a homeomorphism, so preimages of compact sets are compact.
  let θh : GeneralLinear n E ≃ₜ GeneralLinear n E :=
    ((Homeomorph.mulRight y).trans (entrywiseContinuousAut σ n).toHomeomorph).trans
      (Homeomorph.mulLeft g⁻¹)
  have hθh : ⇑θh = θ := rfl
  have hC : IsCompact (θ ⁻¹' tsupport φ) := by
    rw [← hθh]
    exact θh.isCompact_preimage.mpr hφ
  have hP : IsCompact {p : B.parabolic E | (p : GeneralLinear n E) ∈ θ ⁻¹' tsupport φ} :=
    (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hS : IsCompact (B.leviProjection E '' {p : B.parabolic E |
      (p : GeneralLinear n E) ∈ θ ⁻¹' tsupport φ}) :=
    hP.image (B.leviProjectionContinuous E).continuous
  refine HasCompactSupport.intro hS fun m hm => ?_
  have hzero : ∀ u : B.unipotentSubgroup E, φ (g⁻¹ * entrywiseAut σ n
      (B.leviEmbedding E m * (u : GeneralLinear n E) * y)) = 0 := by
    intro u
    by_contra hne
    apply hm
    refine ⟨parabolicProduct B (m, u), ?_, leviProjection_parabolicProduct B (m, u)⟩
    exact subset_tsupport φ hne
  simp only [kernelValue, hzero, integral_zero, mul_zero]

omit [TopologicalSpace F] [IsModuleTopology F E] in
/-- Covariance of the kernel in `g`: for `q` in the parabolic with Levi part `m_q`,
`k(σ(q) g, y)(m) = δ_P(m_q)^{1/2} k(g, y)(m_q⁻¹ m)`. -/
theorem kernelValue_entrywiseAut_mul (μU : Measure (B.unipotentSubgroup E))
    [μU.IsMulLeftInvariant] (φ : GeneralLinear n E → ℂ) (q : B.parabolic E)
    (g y : GeneralLinear n E) (m : B.Levi E) :
    kernelValue σ B μU φ (entrywiseAut σ n q * g) y m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B (B.leviProjection E q) : ℂ) *
        kernelValue σ B μU φ g y ((B.leviProjection E q)⁻¹ * m) := by
  set mq := B.leviProjection E q
  set m' := mq⁻¹ * m
  let uq : B.unipotentSubgroup E := parabolicUnipotentPart B q
  have hq : (q : GeneralLinear n E) = B.leviEmbedding E mq * uq :=
    (congrArg Subtype.val ((parabolicProductEquiv (R := E) B).right_inv q)).symm
  let c : B.unipotentSubgroup E := ⟨(B.leviEmbedding E m')⁻¹ * (uq : GeneralLinear n E)⁻¹ *
      B.leviEmbedding E m', leviEmbedding_conj_mem_unipotentSubgroup B m'
        ((B.unipotentSubgroup E).inv_mem uq.property)⟩
  have hpt : ∀ u : B.unipotentSubgroup E,
      φ ((entrywiseAut σ n q * g)⁻¹ * entrywiseAut σ n
        (B.leviEmbedding E m * (u : GeneralLinear n E) * y)) =
      φ (g⁻¹ * entrywiseAut σ n (B.leviEmbedding E m' * ((c * u : B.unipotentSubgroup E) :
        GeneralLinear n E) * y)) := by
    intro u
    congr 1
    have hm : m = mq * m' := by simp [m']
    have harg : (q : GeneralLinear n E)⁻¹ * (B.leviEmbedding E m * (u : GeneralLinear n E) * y) =
        B.leviEmbedding E m' * ((c * u : B.unipotentSubgroup E) : GeneralLinear n E) * y := by
      rw [hq, hm, map_mul]
      simp only [c, Subgroup.coe_mul]
      group
    rw [mul_inv_rev, mul_assoc, ← map_inv, ← map_mul, harg]
  have hint : (∫ u, φ ((entrywiseAut σ n q * g)⁻¹ * entrywiseAut σ n
        (B.leviEmbedding E m * (u : GeneralLinear n E) * y)) ∂μU) =
      ∫ u, φ (g⁻¹ * entrywiseAut σ n (B.leviEmbedding E m' * (u : GeneralLinear n E) * y))
        ∂μU := by
    simp_rw [hpt]
    exact integral_mul_left_eq_self (fun v : B.unipotentSubgroup E => φ (g⁻¹ *
      entrywiseAut σ n (B.leviEmbedding E m' * (v : GeneralLinear n E) * y))) c
  have hδ : ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) =
      ((LocalFieldData.ofInstances E).leviHalfModulus B mq : ℂ) *
        ((LocalFieldData.ofInstances E).leviHalfModulus B m' : ℂ) := by
    rw [← Units.val_mul, ← map_mul]
    simp [m']
  unfold kernelValue
  rw [hint, hδ, mul_assoc]

end Kernel

end Langlands.BaseChange.TwistedVanDijk
