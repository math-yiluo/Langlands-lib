import Langlands.BaseChange.TwistedVanDijk.KernelFunction
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.Tensor.FiniteProperties

/-! # The kernel operators of the twisted van Dijk formula

For a test function `φ` on `G = GL_n(E)` invariant on both sides under a `σ`-stable compact
open subgroup `K' ⊆ GL_n(𝒪_E)`, the kernel values are test functions on the Levi, and the
operators `A₁ ⊗ ⋯ ⊗ A_r ∘ τ(k(g, y))` assemble into a linear map from functions on
`GL_n(𝒪_E)/K'` to the normalized product induction. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory Measure GeneralLinear HarmonicAnalysis
open scoped ENNReal NNReal

universe u v uW

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ}

/-- A level for a test function `φ`: a compact open subgroup `K'` of `GL_n(𝒪_E)`, stable under
`σ` and `σ⁻¹`, under which `φ` is invariant on both sides. -/
structure Level (φ : GeneralLinear n E → ℂ) where
  /-- The subgroup. -/
  K' : OpenSubgroup (GeneralLinear n E)
  le : (K' : Subgroup (GeneralLinear n E)) ≤ integralGL E n
  sigma_mem : ∀ k ∈ K', entrywiseAut σ n k ∈ K'
  sigma_symm_mem : ∀ k ∈ K', entrywiseAut σ.symm n k ∈ K'
  left : ∀ k ∈ K', ∀ x, φ (k * x) = φ x
  right : ∀ x, ∀ k ∈ K', φ (x * k) = φ x

variable (B : BlockShape n)
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]

/-- The kernel value as a test function on the Levi. -/
def kernelTest {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (g y : GeneralLinear n E) : SchwartzBruhat (B.Levi E) :=
  ⟨kernelValue σ B μU φ g y,
    isLocallyConstant_kernelValue σ B μU L.K'.isOpen L.right g y,
    hasCompactSupport_kernelValue σ B μU φ.hasCompactSupport g y⟩

omit [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] in
@[simp]
theorem kernelTest_apply {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (g y : GeneralLinear n E) (m : B.Levi E) :
    kernelTest σ B μU L g y m = kernelValue σ B μU φ g y m := rfl

variable (μM : Measure (B.Levi E)) [μM.IsHaarMeasure] (hP : ∀ i, IsAdmissible (P i))
  (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i))

/-- The kernel operator `(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(k(g, y))` on the Levi tensor space. -/
def kernelOperator {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (g y : GeneralLinear n E) : Module.End ℂ (PiTensorProduct ℂ W) :=
  (leviTensorIntertwiner σ B A).toLinearMap ∘ₗ
    Hecke.integratedAction μM (B.blockTensor P) (FiniteTensor.isAdmissible_external P hP).1
      (kernelTest σ B μU L g y)

/-- Covariance of the kernel operator in `g` under the parabolic. -/
theorem kernelOperator_mul {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (p : B.parabolic E) (g y : GeneralLinear n E) :
    kernelOperator σ B μU μM hP A L (p * g) y =
      ((LocalFieldData.ofInstances E).leviHalfModulus B (B.leviProjection E p) : ℂ) •
        (B.blockTensor P (B.leviProjection E p) ∘ₗ kernelOperator σ B μU μM hP A L g y) := by
  set q := (parabolicAut σ B).symm p
  have hqp : parabolicAut σ B q = p := MulEquiv.apply_symm_apply _ p
  have hpq : (p : GeneralLinear n E) = entrywiseAut σ n q := by
    rw [← hqp, coe_parabolicAut]
  have hproj : B.leviProjection E p = leviAut σ B (B.leviProjection E q) := by
    rw [← hqp, leviProjection_parabolicAut]
  have hδ : ((LocalFieldData.ofInstances E).leviHalfModulus B (B.leviProjection E p) : ℂ) =
      ((LocalFieldData.ofInstances E).leviHalfModulus B (B.leviProjection E q) : ℂ) := by
    rw [hproj, LocalFieldData.leviHalfModulus_apply, LocalFieldData.leviHalfModulus_apply,
      leviModulus_leviAut]
  have htest : kernelTest σ B μU L (p * g) y =
      ((LocalFieldData.ofInstances E).leviHalfModulus B (B.leviProjection E q) : ℂ) •
        Hecke.TestFunction.leftTranslate (B.leviProjection E q) (kernelTest σ B μU L g y) := by
    apply Subtype.ext
    funext m
    change kernelValue σ B μU φ ((p : GeneralLinear n E) * g) y m = _ * kernelValue σ B μU φ g y _
    rw [hpq, kernelValue_entrywiseAut_mul]
    rfl
  apply LinearMap.ext
  intro v
  simp only [kernelOperator, LinearMap.comp_apply, LinearMap.smul_apply, htest, map_smul,
    LinearMap.smul_apply, Hecke.integratedAction_leftTranslate, hδ]
  congr 1
  rw [hproj]
  exact LinearMap.congr_fun ((leviTensorIntertwiner σ B A).isIntertwining' _) _

omit [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] in
/-- Left invariance of `φ` under the level makes the kernel test function right invariant in
`g`. -/
theorem kernelTest_mul_right_left {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (g y : GeneralLinear n E) {k : GeneralLinear n E} (hk : k ∈ L.K') :
    kernelTest σ B μU L (g * k) y = kernelTest σ B μU L g y := by
  apply Subtype.ext
  funext m
  exact kernelValue_mul_right_left σ B μU L.left g y hk m

omit [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] in
/-- Right invariance of `φ` under the level makes the kernel test function right invariant in
`y`. -/
theorem kernelTest_mul_right_right {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (g y : GeneralLinear n E) {k : GeneralLinear n E} (hk : k ∈ L.K') :
    kernelTest σ B μU L g (y * k) = kernelTest σ B μU L g y := by
  apply Subtype.ext
  funext m
  exact kernelValue_mul_right_right σ B μU (fun k hk x => L.right x k hk) L.sigma_mem g y hk m

variable {σ} in
/-- The level as a subgroup of `GL_n(𝒪_E)`. -/
abbrev Level.inner {φ : GeneralLinear n E → ℂ} (L : Level σ φ) : Subgroup (integralGL E n) :=
  (L.K' : Subgroup (GeneralLinear n E)).subgroupOf (integralGL E n)

variable {σ} in
/-- The cosets `GL_n(𝒪_E) / K'`. -/
abbrev Level.Cosets {φ : GeneralLinear n E → ℂ} (L : Level σ φ) := integralGL E n ⧸ L.inner

variable {σ} in
/-- The cosets of the level form a finite type. -/
noncomputable instance Level.cosetsFintype {φ : GeneralLinear n E → ℂ} (L : Level σ φ) :
    Fintype L.Cosets := by
  have : CompactSpace (integralGL E n) := integralGL_compactSpace n
  have : Finite L.Cosets := Subgroup.quotient_finite_of_isOpen _
    (L.K'.isOpen.preimage continuous_subtype_val)
  exact Fintype.ofFinite _

variable {σ} in
/-- The chosen representative in `GL_n(E)` of a coset of the level. -/
def Level.rep {φ : GeneralLinear n E → ℂ} (L : Level σ φ) (x : L.Cosets) : GeneralLinear n E :=
  ((Quotient.out x : integralGL E n) : GeneralLinear n E)

variable (μK : Measure (integralGL E n))

/-- The function `g ↦ ∑_x c (A₁ ⊗ ⋯ ⊗ A_r) τ(k(g, x)) f(x)`, with `c` the mass of the level. -/
def compactSum {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (f : L.Cosets → PiTensorProduct ℂ W) (g : GeneralLinear n E) : PiTensorProduct ℂ W :=
  ∑ x : L.Cosets, (μK.real (L.inner : Set (integralGL E n)) : ℂ) •
    kernelOperator σ B μU μM hP A L g (L.rep x) (f x)

theorem compactSum_mul_left {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (f : L.Cosets → PiTensorProduct ℂ W) (p : B.parabolic E) (g : GeneralLinear n E) :
    compactSum σ B μU μM hP A μK L f (p * g) =
      twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
        ((B.blockTensor P).comp (B.leviProjection E)) p (compactSum σ B μU μM hP A μK L f g) := by
  simp only [compactSum, kernelOperator_mul, LinearMap.smul_apply, LinearMap.comp_apply,
    _root_.map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x _
  rfl

theorem compactSum_mul_right {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (f : L.Cosets → PiTensorProduct ℂ W) (g : GeneralLinear n E) {k : GeneralLinear n E}
    (hk : k ∈ L.K') :
    compactSum σ B μU μM hP A μK L f (g * k) = compactSum σ B μU μM hP A μK L f g := by
  simp only [compactSum, kernelOperator, kernelTest_mul_right_left σ B μU L g _ hk]

/-- The linear map `S'` from functions on the cosets of the level to the normalized product
induction. -/
def compactOperator {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ) :
    (L.Cosets → PiTensorProduct ℂ W) →ₗ[ℂ]
      Induction.SmoothFunctions (B.parabolic E)
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E))) where
  toFun f := Induction.smoothFunctionOf (B.parabolic E) _ (compactSum σ B μU μM hP A μK L f)
    (fun p x => compactSum_mul_left σ B μU μM hP A μK L f p x) L.K'
    (fun k x => compactSum_mul_right σ B μU μM hP A μK L f x k.property)
  map_add' f f' := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change compactSum σ B μU μM hP A μK L (f + f') g =
      compactSum σ B μU μM hP A μK L f g + compactSum σ B μU μM hP A μK L f' g
    simp only [compactSum, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change compactSum σ B μU μM hP A μK L (a • f) g = a • compactSum σ B μU μM hP A μK L f g
    simp only [compactSum, Pi.smul_apply, map_smul, Finset.smul_sum, smul_comm a]

@[simp]
theorem eval_compactOperator {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (f : L.Cosets → PiTensorProduct ℂ W) (g : GeneralLinear n E) :
    Induction.eval (B.parabolic E)
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E)))
        (compactOperator σ B μU μM hP A μK L f) g =
      compactSum σ B μU μM hP A μK L f g := rfl

/-- The values of `S'` are fixed by the level. -/
theorem compactOperator_mem_fixedVectors {φ : SchwartzBruhat (GeneralLinear n E)}
    (L : Level σ ⇑φ) (f : L.Cosets → PiTensorProduct ℂ W) :
    compactOperator σ B μU μM hP A μK L f ∈
      fixedVectors ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
        (L.K' : Subgroup (GeneralLinear n E)) := by
  intro k
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact compactSum_mul_right σ B μU μM hP A μK L f g k.property

end Langlands.BaseChange.TwistedVanDijk
