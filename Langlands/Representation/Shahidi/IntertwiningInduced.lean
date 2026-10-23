import Langlands.Representation.Shahidi.IntertwiningCovariance
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Tensor.FiniteEquivalences
import Langlands.Representation.Category.Contragredient

/-!
# Shahidi's intertwining operator on the induced spaces

Shahidi's operator `A(s, π, w_{m,n})` of (0.1) on the induced spaces of
`Langlands.Representation.Shahidi.Induction`: the tensor flip `V₁ ⊗ V₂ ≃ V₂ ⊗ V₁`, the
exponent bookkeeping, the operator between arbitrary covariant smooth function spaces
satisfying explicit covariance and Jacobian laws, and its specialization
`I(s, π₁ ⊗ π₂) → I(-s, π₂ ⊗ π₁)` on the convergence domain.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shahidi

universe uR uG uV uW uF

open GeneralLinear
open scoped NNReal

section PairTensor

variable {R : Type uR} [CommRing R]
variable (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable (W : Fin 2 → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

/-- A two-factor indexed tensor is the binary tensor of its two factors. -/
def pairSplit : PiTensorProduct R V ≃ₗ[R] (V 0 ⊗[R] V 1) :=
  (FiniteTensor.headTailLinearEquiv R V).trans
    (TensorProduct.congr (LinearEquiv.refl R (V 0))
      (PiTensorProduct.subsingletonEquiv (R := R) (s := fun j : Fin 1 => V j.succ) 0))

@[simp]
theorem pairSplit_tprod (v : ∀ i, V i) :
    pairSplit V (PiTensorProduct.tprod R v) = v 0 ⊗ₜ[R] v 1 := by
  simp only [pairSplit, LinearEquiv.trans_apply, FiniteTensor.headTailLinearEquiv_tprod,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

variable {V W}

/-- The exchange of the two factors, `x ⊗ y ↦ b y ⊗ a x`, for linear equivalences
`a : V 0 ≃ W 1` and `b : V 1 ≃ W 0`. -/
def pairSwap (a : V 0 ≃ₗ[R] W 1) (b : V 1 ≃ₗ[R] W 0) :
    PiTensorProduct R V ≃ₗ[R] PiTensorProduct R W :=
  (pairSplit V).trans (((TensorProduct.comm R (V 0) (V 1)).trans
    (TensorProduct.congr b a)).trans (pairSplit W).symm)

theorem pairSplit_pairSwap (a : V 0 ≃ₗ[R] W 1) (b : V 1 ≃ₗ[R] W 0)
    (x : PiTensorProduct R V) :
    pairSplit W (pairSwap a b x) =
      TensorProduct.congr b a (TensorProduct.comm R (V 0) (V 1) (pairSplit V x)) := by
  simp [pairSwap]

/-- On pure tensors, `pairSwap` exchanges the factors. -/
theorem pairSwap_tprod (a : V 0 ≃ₗ[R] W 1) (b : V 1 ≃ₗ[R] W 0) (v : ∀ i, V i)
    (w : ∀ i, W i) (h₀ : w 0 = b (v 1)) (h₁ : w 1 = a (v 0)) :
    pairSwap a b (PiTensorProduct.tprod R v) = PiTensorProduct.tprod R w := by
  apply (pairSplit W).injective
  rw [pairSplit_pairSwap, pairSplit_tprod, pairSplit_tprod, h₀, h₁]
  simp

section Actions

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)]
variable {H' : Fin 2 → Type uG} [∀ i, Group (H' i)]

theorem pairSplit_external (ρ : ∀ i, Representation R (H i) (V i)) (h : ∀ i, H i)
    (x : PiTensorProduct R V) :
    pairSplit V (FiniteTensor.external ρ h x) =
      TensorProduct.map (ρ 0 (h 0)) (ρ 1 (h 1)) (pairSplit V x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, FiniteTensor.external_tprod, pairSplit_tprod,
      TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- `pairSwap` intertwines block actions whose factors are exchanged: if `a`
intertwines `ρ 0 (h 0)` with `ρ' 1 (h' 1)` and `b` intertwines `ρ 1 (h 1)` with
`ρ' 0 (h' 0)`, then `pairSwap a b` intertwines the external actions of `h` and
`h'`. -/
theorem pairSwap_external (ρ : ∀ i, Representation R (H i) (V i))
    (ρ' : ∀ i, Representation R (H' i) (W i)) (a : V 0 ≃ₗ[R] W 1) (b : V 1 ≃ₗ[R] W 0)
    (h : ∀ i, H i) (h' : ∀ i, H' i)
    (ha : ∀ x, a (ρ 0 (h 0) x) = ρ' 1 (h' 1) (a x))
    (hb : ∀ y, b (ρ 1 (h 1) y) = ρ' 0 (h' 0) (b y)) (x : PiTensorProduct R V) :
    pairSwap a b (FiniteTensor.external ρ h x) =
      FiniteTensor.external ρ' h' (pairSwap a b x) := by
  apply (pairSplit W).injective
  rw [pairSplit_pairSwap, pairSplit_external, pairSplit_external, pairSplit_pairSwap]
  induction pairSplit V x using TensorProduct.inductionOn with
  | tmul y z => simp [ha, hb]
  | add y z hy hz => simp only [map_add, hy, hz]

end Actions

end PairTensor

/-! ## The flip `V₁ ⊗ V₂ ≃ V₂ ⊗ V₁` and the pair representations -/

section Flip

variable {F : Type uF} [CommRing F]
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

/-- The flip `v₁ ⊗ v₂ ↦ v₂ ⊗ v₁` of the two-factor tensor carriers. -/
def pairFlip : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] PiTensorProduct ℂ (pairCarrier V₂ V₁) :=
  pairSwap (V := pairCarrier V₁ V₂) (W := pairCarrier V₂ V₁) (LinearEquiv.refl ℂ V₁)
    (LinearEquiv.refl ℂ V₂)

@[simp]
theorem pairFlip_pairTensor (v₁ : V₁) (v₂ : V₂) :
    pairFlip (pairTensor v₁ v₂) = pairTensor v₂ v₁ :=
  pairSwap_tprod _ _ _ _ rfl rfl

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂)

/-- `π₁ ⊗ π₂` as a representation of the Levi `GL_m × GL_n` of `twoBlocks m n`. -/
abbrev pairRepresentation :
    Representation ℂ ((twoBlocks m n hm hn).Levi F) (PiTensorProduct ℂ (pairCarrier V₁ V₂)) :=
  (twoBlocks m n hm hn).blockTensor (pairFamily π₁ π₂)

/-- The flip intertwines `π₁ ⊗ π₂` at `(h₁, h₂)` with `π₂ ⊗ π₁` at `(h₂, h₁)`. -/
theorem pairFlip_pairRepresentation (l : (twoBlocks n m hn hm).Levi F)
    (v : PiTensorProduct ℂ (pairCarrier V₁ V₂)) :
    pairFlip (pairRepresentation hm hn π₁ π₂ (twoBlockLeviSwap hm hn F l) v) =
      pairRepresentation hn hm π₂ π₁ l (pairFlip v) :=
  pairSwap_external (pairFamily π₁ π₂) (pairFamily π₂ π₁) _ _ _ _
    (fun _ => rfl) (fun _ => rfl) v

end Flip

/-! ## Exponents -/

section Scalars

variable {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
  (s : ℂ)

/-- The covariance scalar `|det h₁|^((s+n)/2) |det h₂|^(-(s+m)/2)` of `I(s, π₁ ⊗ π₂)`
on the Levi `GL_m × GL_n`. -/
def sourceScalar (l : (twoBlocks m n hm hn).Levi F) : ℂ :=
  (((abv (Matrix.det (l 0).val) : ℝ) : ℂ) ^ ((s + n) / 2)) *
    (((abv (Matrix.det (l 1).val) : ℝ) : ℂ) ^ (-((s + m) / 2)))

/-- The covariance scalar `|det h₂|^((m-s)/2) |det h₁|^((s-n)/2)` of `I(-s, π₂ ⊗ π₁)`
on the Levi `GL_n × GL_m`. -/
def targetScalar (l : (twoBlocks n m hn hm).Levi F) : ℂ :=
  (((abv (Matrix.det (l 0).val) : ℝ) : ℂ) ^ ((m - s) / 2)) *
    (((abv (Matrix.det (l 1).val) : ℝ) : ℂ) ^ ((s - n) / 2))

/-- The exponent bookkeeping of the intertwining integral: the source scalar at the
exchanged Levi element, times the Jacobian `|det h₂|^m / |det h₁|^n` of
`a ↦ h₂⁻¹ a h₁`, is the target scalar. -/
theorem sourceScalar_swap_mul_leviModulus (l : (twoBlocks n m hn hm).Levi F) :
    sourceScalar abv hm hn s (twoBlockLeviSwap hm hn F l) *
        (((leviModulus abv (twoBlocks n m hn hm) l : ℝ≥0) : ℝ) : ℂ) =
      targetScalar abv hm hn s l := by
  rw [leviModulus_twoBlocks]
  set x := determinantAbs abv n (l 0)
  set y := determinantAbs abv m (l 1)
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr x.ne_zero)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr y.ne_zero)
  have hx' : (((x : ℝ≥0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hy' : (((y : ℝ≥0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hxv : ((x : ℝ≥0) : ℝ) = abv (Matrix.det (l 0).val) := rfl
  have hyv : ((y : ℝ≥0) : ℝ) = abv (Matrix.det (l 1).val) := rfl
  simp only [sourceScalar, targetScalar, twoBlockLeviSwap_first, twoBlockLeviSwap_second,
    ← hxv, ← hyv, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, NNReal.coe_div,
    NNReal.coe_pow, Complex.ofReal_div, Complex.ofReal_pow]
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast (((y : ℝ≥0) : ℝ) : ℂ)]
  rw [show (m - s) / 2 = -((s + m) / 2) + (m : ℂ) by ring,
    show (s - n) / 2 = (s + n) / 2 - (n : ℂ) by ring, Complex.cpow_add _ _ hx',
    Complex.cpow_sub _ _ hy']
  field_simp
  rw [hxv, hyv, mul_comm]
  rfl


end Scalars

/-! ## The covariance laws of the inducing data and the Jacobian law -/

section Laws

open MeasureTheory

variable {F : Type uF} [Field F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂) (abv : AbsoluteValue F ℝ) (s : ℂ)

/-- The source covariance law: `σ(p) = |det p₁|^((s+n)/2) |det p₂|^(-(s+m)/2) (π₁ ⊗ π₂)(p₁, p₂)`,
with `(p₁, p₂)` the Levi projection of `p`. -/
def IsSourceCovariance
    (σ : Representation ℂ ((twoBlocks m n hm hn).parabolic F)
      (PiTensorProduct ℂ (pairCarrier V₁ V₂))) : Prop :=
  ∀ (p : (twoBlocks m n hm hn).parabolic F) (v : PiTensorProduct ℂ (pairCarrier V₁ V₂)),
    σ p v = sourceScalar abv hm hn s ((twoBlocks m n hm hn).leviProjection F p) •
      pairRepresentation hm hn π₁ π₂ ((twoBlocks m n hm hn).leviProjection F p) v

/-- The target covariance law on the `(n,m)` parabolic, written through `swapRank`:
`σ'(p) = |det p₁|^((m-s)/2) |det p₂|^((s-n)/2) (π₂ ⊗ π₁)(p₁, p₂)`. -/
def IsTargetCovariance
    (σ' : Representation ℂ ((swappedTwoBlocks m n hm hn).parabolic F)
      (PiTensorProduct ℂ (pairCarrier V₂ V₁))) : Prop :=
  ∀ (p : (twoBlocks n m hn hm).parabolic F) (v : PiTensorProduct ℂ (pairCarrier V₂ V₁)),
    σ' (swappedParabolicEquiv hm hn F p) v =
      targetScalar abv hm hn s ((twoBlocks n m hn hm).leviProjection F p) •
        pairRepresentation hn hm π₂ π₁ ((twoBlocks n m hn hm).leviProjection F p) v

variable [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]
  (μ : Measure (Matrix (Fin n) (Fin m) F))

/-- The Jacobian law: `a ↦ h₂⁻¹ a h₁` multiplies `μ` by the modulus `|det h₂|^m / |det h₁|^n`
of the `(n,m)` Levi. -/
def IsModulusScaling : Prop :=
  ∀ l : (twoBlocks n m hn hm).Levi F,
    μ.map (rectangularConj (l 0) (l 1)) = (leviModulus abv (twoBlocks n m hn hm) l : ℝ≥0) • μ

end Laws

/-! ## The intertwining operator between covariant function spaces -/

section Operator

open MeasureTheory HarmonicAnalysis SmoothWeakIntegral

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂)
variable (μ : Measure (Matrix (Fin n) (Fin m) F))

/-- The underlying functions of a smooth induced space, as a linear map. -/
abbrev inducedFunction {G : Type uF} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type uV} [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) :
    Induction.SmoothFunctions P σ →ₗ[ℂ] (G → W) :=
  (Submodule.subtype _).comp (Submodule.subtype _)

/-- The convergence domain of (0.1) inside a space of `(m,n)`-covariant smooth functions:
the functions for which the weak integral `∫ f(w u' g) du'` exists at every `g`, tested by
the smooth functionals of `π₁ ⊗ π₂`. -/
def convergenceDomain
    (σ : Representation ℂ ((twoBlocks m n hm hn).parabolic F)
      (PiTensorProduct ℂ (pairCarrier V₁ V₂))) :
    Submodule ℂ (Induction.SmoothFunctions ((twoBlocks m n hm hn).parabolic F) σ) :=
  (intertwiningDomain m n (pairRepresentation hm hn π₁ π₂) μ).comap
    (inducedFunction ((twoBlocks m n hm hn).parabolic F) σ)

theorem mem_convergenceDomain
    {σ : Representation ℂ ((twoBlocks m n hm hn).parabolic F)
      (PiTensorProduct ℂ (pairCarrier V₁ V₂))}
    (f : Induction.SmoothFunctions ((twoBlocks m n hm hn).parabolic F) σ) :
    f ∈ convergenceDomain hm hn π₁ π₂ μ σ ↔
      Induction.eval _ σ f ∈ intertwiningDomain m n (pairRepresentation hm hn π₁ π₂) μ :=
  Iff.rfl

/-- The convergence domain is stable under right translation. -/
theorem smoothInduced_mem_convergenceDomain
    {σ : Representation ℂ ((twoBlocks m n hm hn).parabolic F)
      (PiTensorProduct ℂ (pairCarrier V₁ V₂))}
    {f : Induction.SmoothFunctions ((twoBlocks m n hm hn).parabolic F) σ}
    (hf : f ∈ convergenceDomain hm hn π₁ π₂ μ σ) (g : GeneralLinear (m + n) F) :
    Induction.smoothInduced _ σ g f ∈ convergenceDomain hm hn π₁ π₂ μ σ :=
  rightTranslate_mem_intertwiningDomain hf g

variable (hcofinal : CompactOpenCofinal ((twoBlocks m n hm hn).Levi F))
  {π₁ π₂} (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂)

omit [IsTopologicalRing F] [MeasurableSpace F] in
include hπ₁ hπ₂ in
theorem isSmooth_pairRepresentation : IsSmooth (pairRepresentation hm hn π₁ π₂) :=
  FiniteTensor.isSmooth_external _ (fun i => Fin.cases hπ₁ (fun j => Fin.cases hπ₂
    (fun k => k.elim0) j) i)

variable {σ : Representation ℂ ((twoBlocks m n hm hn).parabolic F)
  (PiTensorProduct ℂ (pairCarrier V₁ V₂))}

/-- `g ↦ flip (A f g)`: the intertwining integral of `f`, with its values carried to
`V₂ ⊗ V₁`. -/
def swappedIntegral :
    convergenceDomain hm hn π₁ π₂ μ σ →ₗ[ℂ]
      (GeneralLinear (m + n) F → PiTensorProduct ℂ (pairCarrier V₂ V₁)) :=
  (LinearMap.compLeft (pairFlip : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] _).toLinearMap
      (GeneralLinear (m + n) F)).comp
    ((intertwiningOperator m n (pairRepresentation hm hn π₁ π₂) μ hcofinal
        (isSmooth_pairRepresentation hm hn hπ₁ hπ₂)).comp
      (LinearMap.codRestrict _ ((inducedFunction _ σ).comp (Submodule.subtype _))
        (fun f => f.property)))

theorem swappedIntegral_apply (f : convergenceDomain hm hn π₁ π₂ μ σ)
    (g : GeneralLinear (m + n) F) :
    swappedIntegral hm hn μ hcofinal hπ₁ hπ₂ f g =
      pairFlip (intertwiningOperator m n (pairRepresentation hm hn π₁ π₂) μ hcofinal
        (isSmooth_pairRepresentation hm hn hπ₁ hπ₂) ⟨Induction.eval _ σ f.val, f.property⟩ g) :=
  rfl

section Target

variable [MeasurableAdd₂ F] [MeasurableMul F] [μ.IsAddLeftInvariant]
variable {μ} {abv : AbsoluteValue F ℝ} {s : ℂ}

/-- The swapped integral transforms under the `(n,m)` parabolic with the target exponents. -/
theorem swappedIntegral_swapRank_mul (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hμ : IsModulusScaling hm hn abv μ) (f : convergenceDomain hm hn π₁ π₂ μ σ)
    (p : (twoBlocks n m hn hm).parabolic F) (x : GeneralLinear (m + n) F) :
    swappedIntegral hm hn μ hcofinal hπ₁ hπ₂ f (swapRank m n F p * x) =
      targetScalar abv hm hn s ((twoBlocks n m hn hm).leviProjection F p) •
        pairRepresentation hn hm π₂ π₁ ((twoBlocks n m hn hm).leviProjection F p)
          (swappedIntegral hm hn μ hcofinal hπ₁ hπ₂ f x) := by
  rw [swappedIntegral_apply, swappedIntegral_apply,
    intertwiningOperator_parabolic hm hn hcofinal (isSmooth_pairRepresentation hm hn hπ₁ hπ₂)
      ⟨Induction.eval _ σ f.val, f.property⟩ (sourceScalar abv hm hn s) id
      (fun p x => (f.val.1.2 p x).trans (hσ p _))
      (fun l => (leviModulus abv (twoBlocks n m hn hm) l : ℝ≥0)) hμ p x,
    map_smul, id, pairFlip_pairRepresentation, sourceScalar_swap_mul_leviModulus]

variable {σ' : Representation ℂ ((swappedTwoBlocks m n hm hn).parabolic F)
  (PiTensorProduct ℂ (pairCarrier V₂ V₁))}

theorem swappedIntegral_mem_coindV (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hσ' : IsTargetCovariance hm hn π₁ π₂ abv s σ') (hμ : IsModulusScaling hm hn abv μ)
    (f : convergenceDomain hm hn π₁ π₂ μ σ) :
    swappedIntegral hm hn μ hcofinal hπ₁ hπ₂ f ∈
      Representation.coindV ((swappedTwoBlocks m n hm hn).parabolic F).subtype σ' := by
  rw [Representation.mem_coindV]
  intro p' x
  have hp : (((swappedTwoBlocks m n hm hn).parabolic F).subtype p' : GeneralLinear (m + n) F) =
      swapRank m n F ((swappedParabolicEquiv hm hn F).symm p') := by
    rw [← swappedParabolicEquiv_coe, MulEquiv.apply_symm_apply]
    rfl
  rw [hp, swappedIntegral_swapRank_mul hm hn hcofinal hπ₁ hπ₂ hσ hμ, ← hσ',
    MulEquiv.apply_symm_apply]

omit [MeasurableAdd₂ F] [MeasurableMul F] [μ.IsAddLeftInvariant] in
theorem swappedIntegral_mul_right (f : convergenceDomain hm hn π₁ π₂ μ σ)
    (k : GeneralLinear (m + n) F)
    (hk : ∀ x, Induction.eval _ σ f.val (x * k) = Induction.eval _ σ f.val x)
    (x : GeneralLinear (m + n) F) :
    swappedIntegral hm hn μ hcofinal hπ₁ hπ₂ f (x * k) =
      swappedIntegral hm hn μ hcofinal hπ₁ hπ₂ f x := by
  rw [swappedIntegral_apply, swappedIntegral_apply, intertwiningOperator_mul_right]
  exact hk

/-- The intertwining integral as a linear map from its convergence domain into the smooth
`(n,m)`-covariant functions: `f ↦ (g ↦ flip ∫_{U'} f(w u' g) du')`. -/
def swappedOperator (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hσ' : IsTargetCovariance hm hn π₁ π₂ abv s σ') (hμ : IsModulusScaling hm hn abv μ) :
    convergenceDomain hm hn π₁ π₂ μ σ →ₗ[ℂ]
      Induction.SmoothFunctions ((swappedTwoBlocks m n hm hn).parabolic F) σ' :=
  LinearMap.codRestrict _ (LinearMap.codRestrict _ (swappedIntegral hm hn μ hcofinal hπ₁ hπ₂)
      (swappedIntegral_mem_coindV hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ))
    (fun f => by
      obtain ⟨K, hK⟩ := f.val.property
      refine ⟨K, ?_⟩
      rw [fixedVectors, Representation.mem_invariants] at hK ⊢
      intro k
      apply Subtype.ext
      funext x
      exact swappedIntegral_mul_right hm hn hcofinal hπ₁ hπ₂ f k
        (fun y => congrFun (congrArg Subtype.val (hK k)) y) x)

theorem swappedOperator_apply (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hσ' : IsTargetCovariance hm hn π₁ π₂ abv s σ') (hμ : IsModulusScaling hm hn abv μ)
    (f : convergenceDomain hm hn π₁ π₂ μ σ) (g : GeneralLinear (m + n) F) :
    Induction.eval _ σ' (swappedOperator hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ f) g =
      pairFlip (intertwiningOperator m n (pairRepresentation hm hn π₁ π₂) μ hcofinal
        (isSmooth_pairRepresentation hm hn hπ₁ hπ₂) ⟨Induction.eval _ σ f.val, f.property⟩ g) :=
  rfl

/-- The value of the operator at `g` is the flip of the weak integral
`∫_{U'} f(w u' g) du'`. -/
theorem hasIntegral_swappedOperator (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hσ' : IsTargetCovariance hm hn π₁ π₂ abv s σ') (hμ : IsModulusScaling hm hn abv μ)
    (f : convergenceDomain hm hn π₁ π₂ μ σ) (g : GeneralLinear (m + n) F) :
    HasIntegral (pairRepresentation hm hn π₁ π₂) μ
      (fun a => Induction.eval _ σ f.val (blockWeyl m n F * intertwiningUnipotent m n F a * g))
      (pairFlip.symm
        (Induction.eval _ σ' (swappedOperator hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ f) g)) := by
  rw [swappedOperator_apply, LinearEquiv.symm_apply_apply]
  exact hasIntertwiningIntegral_intertwiningOperator hcofinal
    (isSmooth_pairRepresentation hm hn hπ₁ hπ₂) ⟨_, f.property⟩ g

/-- Every smooth functional of `π₁ ⊗ π₂`, applied to the flipped value, is the scalar
integral `∫_{U'} ℓ(f(w u' g)) du'`. -/
theorem swappedOperator_eval (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hσ' : IsTargetCovariance hm hn π₁ π₂ abv s σ') (hμ : IsModulusScaling hm hn abv μ)
    (f : convergenceDomain hm hn π₁ π₂ μ σ) (g : GeneralLinear (m + n) F)
    (ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂)) :
    ℓ.val (pairFlip.symm
        (Induction.eval _ σ' (swappedOperator hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ f) g)) =
      ∫ a, ℓ.val (Induction.eval _ σ f.val
        (blockWeyl m n F * intertwiningUnipotent m n F a * g)) ∂μ := by
  rw [swappedOperator_apply, LinearEquiv.symm_apply_apply]
  exact intertwiningOperator_eval hcofinal (isSmooth_pairRepresentation hm hn hπ₁ hπ₂)
    ⟨_, f.property⟩ g ℓ

/-- The operator commutes with right translation. -/
theorem swappedOperator_smoothInduced (hσ : IsSourceCovariance hm hn π₁ π₂ abv s σ)
    (hσ' : IsTargetCovariance hm hn π₁ π₂ abv s σ') (hμ : IsModulusScaling hm hn abv μ)
    (f : convergenceDomain hm hn π₁ π₂ μ σ) (g : GeneralLinear (m + n) F) :
    swappedOperator hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ
        ⟨Induction.smoothInduced _ σ g f.val,
          smoothInduced_mem_convergenceDomain hm hn π₁ π₂ μ f.property g⟩ =
      Induction.smoothInduced _ σ' g (swappedOperator hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact congrArg pairFlip (congrFun (intertwiningOperator_rightTranslate hcofinal
    (isSmooth_pairRepresentation hm hn hπ₁ hπ₂) ⟨_, f.property⟩ g) x)

end Target

end Operator

/-! ## The operator `I(s, π₁ ⊗ π₂) → I(-s, π₂ ⊗ π₁)` -/

section General

open MeasureTheory HarmonicAnalysis SmoothWeakIntegral

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (abv : AbsoluteValue F ℝ) (hopen : IsOpenNormOne abv)
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂)

/-- The inducing representation of `I(s, π₁ ⊗ π₂)` satisfies the source covariance law. -/
theorem isSourceCovariance_source :
    IsSourceCovariance hm hn π₁ π₂ abv s
      ((twoBlocks m n hm hn).inducingRepresentation
        (leviHalfCharacter (twoBlocks m n hm hn) hopen)
        ((twoBlocks m n hm hn).blockTensor (twistedPair abv s π₁ π₂))) := by
  intro p v
  change ((leviHalfCharacter (twoBlocks m n hm hn) hopen).toMonoidHom
      ((twoBlocks m n hm hn).leviProjection F p) : ℂ) •
    (twoBlocks m n hm hn).blockTensor
      (pairFamily (twist (determinantPower abv m (s / 2)) π₁)
        (twist (determinantPower abv n (-(s / 2))) π₂))
      ((twoBlocks m n hm hn).leviProjection F p) v = _
  rw [blockTensor_pairFamily_twist, LinearMap.smul_apply, smul_smul]
  congr 1
  rw [leviHalfCharacter_toMonoidHom, leviHalfModulus_apply, leviModulus_twoBlocks]
  refine (sqrt_mul_cpow_mul_cpow
    (determinantAbs abv m ((twoBlocks m n hm hn).leviProjection F p 0))
    (determinantAbs abv n ((twoBlocks m n hm hn).leviProjection F p 1)) m n
    (s / 2) (-(s / 2))).trans ?_
  rw [show s / 2 + (n : ℂ) / 2 = (s + n) / 2 by ring,
    show -(s / 2) - (m : ℂ) / 2 = -((s + m) / 2) by ring]
  rfl

/-- The inducing representation of `I(-s, π₂ ⊗ π₁)` satisfies the target covariance law. -/
theorem isTargetCovariance_target :
    IsTargetCovariance hm hn π₁ π₂ abv s
      ((swappedTwoBlocks m n hm hn).inducingRepresentation
        (leviHalfCharacter (swappedTwoBlocks m n hm hn) hopen)
        ((swappedTwoBlocks m n hm hn).blockTensor (twistedPair abv (-s) π₂ π₁))) := by
  intro p v
  change ((leviHalfCharacter (swappedTwoBlocks m n hm hn) hopen).toMonoidHom
      ((swappedTwoBlocks m n hm hn).leviProjection F (swappedParabolicEquiv hm hn F p)) : ℂ) •
    (twoBlocks n m hn hm).blockTensor
      (pairFamily (twist (determinantPower abv n (-s / 2)) π₂)
        (twist (determinantPower abv m (-(-s / 2))) π₁))
      ((swappedTwoBlocks m n hm hn).leviProjection F (swappedParabolicEquiv hm hn F p)) v = _
  rw [leviProjection_swappedParabolicEquiv, blockTensor_pairFamily_twist, LinearMap.smul_apply,
    smul_smul]
  congr 1
  rw [leviHalfCharacter_toMonoidHom, leviHalfModulus_apply, leviModulus_swappedTwoBlocks]
  refine (sqrt_mul_cpow_mul_cpow
    (determinantAbs abv n ((twoBlocks n m hn hm).leviProjection F p 0))
    (determinantAbs abv m ((twoBlocks n m hn hm).leviProjection F p 1)) n m
    (-s / 2) (-(-s / 2))).trans ?_
  rw [show -s / 2 + (m : ℂ) / 2 = (m - s) / 2 by ring,
    show -(-s / 2) - (n : ℂ) / 2 = (s - n) / 2 by ring]
  rfl

variable [MeasurableSpace F] (μ : Measure (Matrix (Fin n) (Fin m) F))

/-- The convergence domain of (0.1) in `I(s, π₁ ⊗ π₂)`: the `f` for which
`∫_{U'} f(w_{m,n} u' g) du'` exists as a weak integral at every `g`. -/
abbrev sourceDomain : Submodule ℂ (SourceSpace abv hopen hm hn s π₁ π₂) :=
  convergenceDomain hm hn π₁ π₂ μ
    ((twoBlocks m n hm hn).inducingRepresentation
      (leviHalfCharacter (twoBlocks m n hm hn) hopen)
      ((twoBlocks m n hm hn).blockTensor (twistedPair abv s π₁ π₂)))

/-- The convergence domain is a subrepresentation of `I(s, π₁ ⊗ π₂)`. -/
theorem source_mem_sourceDomain {f : SourceSpace abv hopen hm hn s π₁ π₂}
    (hf : f ∈ sourceDomain abv hopen hm hn s π₁ π₂ μ) (g : GeneralLinear (m + n) F) :
    source abv hopen hm hn s π₁ π₂ g f ∈ sourceDomain abv hopen hm hn s π₁ π₂ μ :=
  smoothInduced_mem_convergenceDomain hm hn π₁ π₂ μ hf g

variable [MeasurableAdd₂ F] [MeasurableMul F] [μ.IsAddLeftInvariant]
variable (hcofinal : CompactOpenCofinal ((twoBlocks m n hm hn).Levi F))
  {π₁ π₂} (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) {μ}
  (hμ : IsModulusScaling hm hn abv μ)

/-- Shahidi's intertwining operator `A(s, π, w_{m,n})` of (0.1), from the convergence
domain in `I(s, π₁ ⊗ π₂)` to `I(-s, π₂ ⊗ π₁)`:
`A f(g) = ∫_{U'} f(w_{m,n} u' g) du'`, with values carried from `V₁ ⊗ V₂` to `V₂ ⊗ V₁`. -/
def intertwiningInduced :
    sourceDomain abv hopen hm hn s π₁ π₂ μ →ₗ[ℂ] TargetSpace abv hopen hm hn s π₁ π₂ :=
  swappedOperator hm hn hcofinal hπ₁ hπ₂ (isSourceCovariance_source abv hopen hm hn s π₁ π₂)
    (isTargetCovariance_target abv hopen hm hn s π₁ π₂) hμ

theorem targetEval_intertwiningInduced (f : sourceDomain abv hopen hm hn s π₁ π₂ μ)
    (g : GeneralLinear (m + n) F) :
    targetEval abv hopen hm hn s π₁ π₂
        (intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ f) g =
      pairFlip (intertwiningOperator m n (pairRepresentation hm hn π₁ π₂) μ hcofinal
        (isSmooth_pairRepresentation hm hn hπ₁ hπ₂)
        ⟨sourceEval abv hopen hm hn s π₁ π₂ f.val, f.property⟩ g) :=
  rfl

/-- `A f(g)` is the flip of the weak integral `∫_{U'} f(w_{m,n} u' g) du'`. -/
theorem hasIntegral_intertwiningInduced (f : sourceDomain abv hopen hm hn s π₁ π₂ μ)
    (g : GeneralLinear (m + n) F) :
    HasIntegral (pairRepresentation hm hn π₁ π₂) μ
      (fun a => sourceEval abv hopen hm hn s π₁ π₂ f.val
        (blockWeyl m n F * intertwiningUnipotent m n F a * g))
      (pairFlip.symm (targetEval abv hopen hm hn s π₁ π₂
        (intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ f) g)) :=
  hasIntegral_swappedOperator hm hn hcofinal hπ₁ hπ₂ _ _ hμ f g

/-- Every smooth functional `ℓ` of `π₁ ⊗ π₂` satisfies
`ℓ(flip⁻¹ A f(g)) = ∫_{U'} ℓ(f(w_{m,n} u' g)) du'`. -/
theorem intertwiningInduced_eval (f : sourceDomain abv hopen hm hn s π₁ π₂ μ)
    (g : GeneralLinear (m + n) F) (ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂)) :
    ℓ.val (pairFlip.symm (targetEval abv hopen hm hn s π₁ π₂
        (intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ f) g)) =
      ∫ a, ℓ.val (sourceEval abv hopen hm hn s π₁ π₂ f.val
        (blockWeyl m n F * intertwiningUnipotent m n F a * g)) ∂μ :=
  swappedOperator_eval hm hn hcofinal hπ₁ hπ₂ _ _ hμ f g ℓ

/-- `A(s, π, w_{m,n})` intertwines `I(s, π₁ ⊗ π₂)` with `I(-s, π₂ ⊗ π₁)` on its domain. -/
theorem intertwiningInduced_source (f : sourceDomain abv hopen hm hn s π₁ π₂ μ)
    (g : GeneralLinear (m + n) F) :
    intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ
        ⟨source abv hopen hm hn s π₁ π₂ g f.val,
          source_mem_sourceDomain abv hopen hm hn s π₁ π₂ μ f.property g⟩ =
      target abv hopen hm hn s π₁ π₂ g
        (intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ f) :=
  swappedOperator_smoothInduced hm hn hcofinal hπ₁ hπ₂ _ _ hμ f g

end General

end Langlands.Shahidi
