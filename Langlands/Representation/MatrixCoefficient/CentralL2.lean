import Langlands.Representation.MatrixCoefficient.CentralInduction
import Langlands.Representation.Unitary.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The actual square-integrable central-character model

The carrier consists of actual smooth covariant functions. The Hermitian
pairing, rather than either covariant function, descends to the full central
quotient.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.Induction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : Subgroup.center G →* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
include hχ in
/-- The product of a conjugated character value and that value is one. -/
theorem centralCharacter_conj_mul (z : Subgroup.center G) :
    conj (χ z : ℂ) * (χ z : ℂ) = 1 := by
  simp [Complex.conj_mul', hχ z]

/-- Descend the Hermitian pairing itself, preserving the central character. -/
def centralPairing (f h : CentralFunctions χ) : G ⧸ Subgroup.center G → ℂ :=
  Quotient.lift (fun g => conj (eval _ _ f g) * eval _ _ h g) (by
    intro a b hab
    have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hab
    let z : Subgroup.center G := ⟨a⁻¹ * b, hz⟩
    have hzb : (z : G) * a = b := by
      rw [z.property.comm a]
      simp [z]
    have hf := eval_covariant (Subgroup.center G) (characterRepresentation χ) f z a
    have hh := eval_covariant (Subgroup.center G) (characterRepresentation χ) h z a
    change eval _ _ f ((z : G) * a) = (χ z : ℂ) * eval _ _ f a at hf
    change eval _ _ h ((z : G) * a) = (χ z : ℂ) * eval _ _ h a at hh
    rw [hzb] at hf hh
    rw [hf, hh, map_mul]
    calc
      conj (eval _ _ f a) * eval _ _ h a =
          (conj (χ z : ℂ) * (χ z : ℂ)) *
            (conj (eval _ _ f a) * eval _ _ h a) := by
              rw [centralCharacter_conj_mul χ hχ, one_mul]
      _ = conj (χ z : ℂ) * conj (eval _ _ f a) *
          ((χ z : ℂ) * eval _ _ h a) := by ring)

omit [IsTopologicalGroup G] in
@[simp]
theorem centralPairing_mk (f h : CentralFunctions χ) (g : G) :
    centralPairing χ hχ f h (QuotientGroup.mk g) =
      conj (eval _ _ f g) * eval _ _ h g := rfl

/-- The descended pairing is locally constant in the actual quotient topology. -/
theorem centralPairing_isLocallyConstant (f h : CentralFunctions χ) :
    IsLocallyConstant (centralPairing χ hχ f h) := by
  intro s
  apply (isQuotientMap_quotient_mk'
    (s := QuotientGroup.leftRel (Subgroup.center G))).isCoinducing.isOpen_preimage.mp
  exact ((eval_isLocallyConstant _ _ f).comp₂ (eval_isLocallyConstant _ _ h)
    (fun a b : ℂ => conj a * b)) s

omit [IsTopologicalGroup G] in
theorem centralNorm_nonneg (f : CentralFunctions χ) (q : G ⧸ Subgroup.center G) :
    0 ≤ centralNorm χ hχ f q := by
  induction q using Quotient.inductionOn
  exact norm_nonneg _

omit [IsTopologicalGroup G] in
theorem norm_centralPairing (f h : CentralFunctions χ) (q : G ⧸ Subgroup.center G) :
    ‖centralPairing χ hχ f h q‖ =
      centralNorm χ hχ f q * centralNorm χ hχ h q := by
  induction q using Quotient.inductionOn
  simp

omit [IsTopologicalGroup G] in
/-- The diagonal is precisely the real norm square, embedded in the complex numbers. -/
theorem centralPairing_self (f : CentralFunctions χ) (q : G ⧸ Subgroup.center G) :
    centralPairing χ hχ f f q = ((centralNorm χ hχ f q) ^ 2 : ℝ) := by
  induction q using Quotient.inductionOn with
  | h g =>
    simpa only [centralPairing_mk, centralNorm_mk, Complex.ofReal_pow] using
      Complex.conj_mul' (eval _ _ f g)

omit [IsTopologicalGroup G] in
theorem centralPairing_conj (f h : CentralFunctions χ) (q : G ⧸ Subgroup.center G) :
    conj (centralPairing χ hχ h f q) = centralPairing χ hχ f h q := by
  induction q using Quotient.inductionOn
  simp [mul_comm]

omit [IsTopologicalGroup G] in
theorem centralPairing_add_left (f h j : CentralFunctions χ)
    (q : G ⧸ Subgroup.center G) :
    centralPairing χ hχ (f + h) j q =
      centralPairing χ hχ f j q + centralPairing χ hχ h j q := by
  induction q using Quotient.inductionOn
  change conj (eval _ _ f _ + eval _ _ h _) * _ = _
  simp [map_add, add_mul]

omit [IsTopologicalGroup G] in
theorem centralPairing_smul_left (f h : CentralFunctions χ) (c : ℂ)
    (q : G ⧸ Subgroup.center G) :
    centralPairing χ hχ (c • f) h q = conj c * centralPairing χ hχ f h q := by
  induction q using Quotient.inductionOn
  change conj (c * eval _ _ f _) * _ = _
  simp [map_mul, mul_assoc]

theorem centralPairing_translate (f h : CentralFunctions χ) (g : G)
    (q : G ⧸ Subgroup.center G) :
    centralPairing χ hχ (centralInduced χ g f) (centralInduced χ g h) q =
      centralPairing χ hχ f h (q * QuotientGroup.mk g) := by
  induction q using Quotient.inductionOn
  rfl

section Measure

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G))

/-- Actual central-character functions with square-integrable quotient norm. -/
def centralL2Submodule : Submodule ℂ (CentralFunctions χ) where
  carrier := {f | MemLp (centralNorm χ hχ f) 2 μ}
  zero_mem' := by
    change MemLp (centralNorm χ hχ (0 : CentralFunctions χ)) 2 μ
    have hz : centralNorm χ hχ (0 : CentralFunctions χ) = 0 := by
      funext q
      induction q using Quotient.inductionOn
      simp [centralNorm_mk, eval]
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro f h hf hh
    apply (hf.add hh).mono'
      (centralNorm_isLocallyConstant χ hχ (f + h)).continuous.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    induction q using Quotient.inductionOn
    change |‖eval _ _ f _ + eval _ _ h _‖| ≤
      ‖eval _ _ f _‖ + ‖eval _ _ h _‖
    rw [abs_of_nonneg (norm_nonneg _)]
    exact norm_add_le _ _
  smul_mem' := by
    intro c f hf
    change MemLp (centralNorm χ hχ (c • f)) 2 μ
    have heq : centralNorm χ hχ (c • f) =
        fun q => ‖c‖ * centralNorm χ hχ f q := by
      funext q
      induction q using Quotient.inductionOn
      change ‖c * eval _ _ f _‖ = ‖c‖ * ‖eval _ _ f _‖
      exact norm_mul _ _
    rw [heq]
    exact hf.const_mul ‖c‖

/-- This is a subspace of actual functions, without quotienting by null functions. -/
abbrev CentralL2 := centralL2Submodule χ hχ μ

@[simp]
theorem mem_centralL2Submodule (f : CentralFunctions χ) :
    f ∈ centralL2Submodule χ hχ μ ↔ MemLp (centralNorm χ hχ f) 2 μ := Iff.rfl

/-- Pointwise evaluation recovers an element of the actual function subspace. -/
theorem centralL2_ext {f h : CentralL2 χ hχ μ}
    (heval : ∀ g, eval _ _ f.1 g = eval _ _ h.1 g) : f = h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact funext heval

/-- The diagonal norm-square is an integrable real function. -/
theorem centralL2_norm_sq_integrable (f : CentralL2 χ hχ μ) :
    Integrable (fun q => (centralNorm χ hχ f.1 q) ^ 2) μ :=
  f.property.integrable_sq

/-- Holder's inequality gives integrability of the actual descended pairing. -/
theorem centralPairing_integrable (f h : CentralL2 χ hχ μ) :
    Integrable (centralPairing χ hχ f.1 h.1) μ := by
  have hprod := f.property.integrable_mul h.property
  apply hprod.mono'
    (centralPairing_isLocallyConstant χ hχ f.1 h.1).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => (norm_centralPairing χ hχ f.1 h.1 q).le

variable [μ.IsMulRightInvariant]

/-- Square-integrability is preserved by the existing right action. -/
def centralL2Subrepresentation : Subrepresentation (centralInduced χ) where
  toSubmodule := centralL2Submodule χ hχ μ
  apply_mem_toSubmodule := by
    intro g f hf
    change MemLp (centralNorm χ hχ (centralInduced χ g f)) 2 μ
    have heq : centralNorm χ hχ (centralInduced χ g f) =
        centralNorm χ hχ f ∘ (fun q => q * QuotientGroup.mk g) :=
      funext (centralNorm_translate χ hχ f g)
    rw [heq]
    exact hf.comp_measurePreserving (measurePreserving_mul_right μ (QuotientGroup.mk g))

/-- The actual right-translation representation on the central L2 subspace. -/
def centralL2Representation : Representation ℂ G (CentralL2 χ hχ μ) :=
  (centralL2Subrepresentation χ hχ μ).toRepresentation

/-- The actual equivariant inclusion into smooth central induction. -/
def centralL2Inclusion :
    (centralL2Representation χ hχ μ).IntertwiningMap (centralInduced χ) where
  toLinearMap := (centralL2Submodule χ hχ μ).subtype
  isIntertwining' _ := by ext f; rfl

theorem centralL2Inclusion_injective : Function.Injective (centralL2Inclusion χ hχ μ) :=
  Subtype.val_injective

@[simp]
theorem centralL2Inclusion_apply (f : CentralL2 χ hχ μ) :
    centralL2Inclusion χ hχ μ f = f.1 := rfl

@[simp]
theorem centralL2Inclusion_eval (f : CentralL2 χ hχ μ) (g : G) :
    eval _ _ (centralL2Inclusion χ hχ μ f) g = eval _ _ f.1 g := rfl

@[simp]
theorem centralL2Inclusion_recover (f : CentralFunctions χ)
    (hf : MemLp (centralNorm χ hχ f) 2 μ) :
    centralL2Inclusion χ hχ μ ⟨f, hf⟩ = f := rfl

@[simp]
theorem centralL2Representation_eval (f : CentralL2 χ hχ μ) (g x : G) :
    eval _ _ (centralL2Representation χ hχ μ g f).1 x = eval _ _ f.1 (x * g) := rfl

theorem centralL2Representation_smooth : IsSmooth (centralL2Representation χ hχ μ) := by
  intro f
  obtain ⟨K, hK⟩ := smoothInduced_smooth
    (Subgroup.center G) (characterRepresentation χ) f.1
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

variable [μ.IsHaarMeasure]

/-- The Bochner integral of the descended pairing is an invariant positive
definite Hermitian form on the actual function subspace. -/
def centralL2Form : InvariantPositiveForm (centralL2Representation χ hχ μ) where
  inner f h := ∫ q, centralPairing χ hχ f.1 h.1 q ∂μ
  conj_inner_symm f h := by
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
      centralPairing_conj χ hχ f.1 h.1 q)
  re_inner_nonneg f := by
    rw [← integral_re (centralPairing_integrable χ hχ μ f f)]
    apply integral_nonneg
    intro q
    change 0 ≤ (centralPairing χ hχ f.1 f.1 q).re
    rw [centralPairing_self]
    simpa only [Complex.ofReal_re] using sq_nonneg (centralNorm χ hχ f.1 q)
  add_left f h j := by
    change (∫ q, centralPairing χ hχ (f.1 + h.1) j.1 q ∂μ) = _
    simp_rw [centralPairing_add_left]
    exact integral_add (centralPairing_integrable χ hχ μ f j)
      (centralPairing_integrable χ hχ μ h j)
  smul_left f h c := by
    change (∫ q, centralPairing χ hχ (c • f.1) h.1 q ∂μ) = _
    simp_rw [centralPairing_smul_left]
    exact integral_const_mul _ _
  definite f hf := by
    have hzero :
        (∫ q, (centralPairing χ hχ f.1 f.1 q).re ∂μ) = 0 := by
      change (∫ q, RCLike.re (centralPairing χ hχ f.1 f.1 q) ∂μ) = 0
      rw [integral_re (centralPairing_integrable χ hχ μ f f), hf]
      rfl
    have hnonneg (q : G ⧸ Subgroup.center G) :
        0 ≤ (centralPairing χ hχ f.1 f.1 q).re := by
      rw [centralPairing_self]
      simpa only [Complex.ofReal_re] using sq_nonneg (centralNorm χ hχ f.1 q)
    have hae : (fun q => (centralPairing χ hχ f.1 f.1 q).re) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg
        (centralPairing_integrable χ hχ μ f f).re).mp hzero
    have heq := Measure.eq_of_ae_eq hae
      ((centralPairing_isLocallyConstant χ hχ f.1 f.1).comp Complex.re).continuous
      continuous_const
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change eval _ _ f.1 g = 0
    have hsquare : ‖eval _ _ f.1 g‖ ^ 2 = 0 := by
      have hq := congrFun heq (QuotientGroup.mk g)
      rw [centralPairing_self] at hq
      simpa only [centralNorm_mk, Complex.ofReal_re, Pi.zero_apply] using hq
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  invariant g f h := by
    change (∫ q, centralPairing χ hχ
      (centralInduced χ g f.1) (centralInduced χ g h.1) q ∂μ) = _
    simp_rw [centralPairing_translate]
    exact integral_mul_right_eq_self _ (QuotientGroup.mk g)

/-- The exact complex-valued quotient-integral formula. -/
theorem centralL2Form_inner (f h : CentralL2 χ hχ μ) :
    (centralL2Form χ hχ μ).inner f h =
      ∫ q, centralPairing χ hχ f.1 h.1 q ∂μ := rfl

/-- The exact diagonal formula as the complex image of a real norm-square integral. -/
theorem centralL2Form_inner_self (f : CentralL2 χ hχ μ) :
    (centralL2Form χ hχ μ).inner f f =
      ((∫ q, (centralNorm χ hχ f.1 q) ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [centralL2Form_inner]
  simp_rw [centralPairing_self]
  exact integral_ofReal

theorem centralL2Form_inner_add_right (f h j : CentralL2 χ hχ μ) :
    (centralL2Form χ hχ μ).inner f (h + j) =
      (centralL2Form χ hχ μ).inner f h + (centralL2Form χ hχ μ).inner f j := by
  let : InnerProductSpace.Core ℂ (CentralL2 χ hχ μ) :=
    (centralL2Form χ hχ μ).toInnerProductCore
  exact InnerProductSpace.Core.inner_add_right f h j

theorem centralL2Form_inner_smul_right (f h : CentralL2 χ hχ μ) (c : ℂ) :
    (centralL2Form χ hχ μ).inner f (c • h) =
      c * (centralL2Form χ hχ μ).inner f h := by
  let : InnerProductSpace.Core ℂ (CentralL2 χ hχ μ) :=
    (centralL2Form χ hχ μ).toInnerProductCore
  exact InnerProductSpace.Core.inner_smul_right f h

end Measure
end Langlands.Induction
