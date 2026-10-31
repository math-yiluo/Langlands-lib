import Langlands.Shimura.PEL.HarrisHodgeCentralTrace
import Langlands.Shimura.PEL.HarrisTaylorLieCondition
import Langlands.Shimura.PEL.HarrisReflexBase
import Mathlib.RingTheory.Trace.Basic

/-! # Arithmetic normalization of the actual Harris Hodge trace -/

noncomputable section
open NumberField _root_.Algebra Module
open scoped TensorProduct Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

/-- The actual embeddings inducing the given imaginary-place embedding sum to the field trace. -/
theorem sum_embeddings_inducing_eq_trace (τ₀ : L →+* ℂ) (a : K) :
    (∑ i : K →+* ℂ, if i.comp (algebraMap L K) = τ₀ then i a else 0) =
      τ₀ (_root_.Algebra.trace L K a) := by
  let : Algebra L ℂ := τ₀.toAlgebra
  let e : (K →ₐ[L] ℂ) ≃ {i : K →+* ℂ // i.comp (algebraMap L K) = τ₀} :=
    { toFun := fun i => ⟨i.toRingHom, by
        ext x
        exact i.commutes x⟩
      invFun := fun i => { i.1 with commutes' := fun x => RingHom.congr_fun i.2 x }
      left_inv := fun i => by ext x; rfl
      right_inv := fun i => by apply Subtype.ext; rfl }
  calc
    _ = ∑ i : {i : K →+* ℂ // i.comp (algebraMap L K) = τ₀}, i.1 a := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        (Finset.univ.filter (fun i : K →+* ℂ => i.comp (algebraMap L K) = τ₀))
        (by intro i; simp) (fun i : K →+* ℂ => i a)
    _ = ∑ i : K →ₐ[L] ℂ, i a :=
      (Fintype.sum_equiv e (fun i => i a) (fun i => i.1 a) (fun _ => rfl)).symm
    _ = τ₀ (_root_.Algebra.trace L K a) :=
      (_root_.trace_eq_sum_embeddings ℂ (x := a)).symm

end Langlands.Shimura.HarrisTaylor

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K] [IsCMField K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L K]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L K) τ₀))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L K) τ₀

omit [IsCMField K] [IsScalarTower ℚ K A] in
/-- The weighted embedding sum of the actual Harris Hodge function. -/
theorem sum_realHodgeFunction_mul_embedding (a : K) :
    (∑ i : K →+* ℂ, (D.realHodgeFunction C i : ℂ) * i a) =
      (n : ℂ) * τ₀ (_root_.Algebra.trace L K a) -
        C.distinguishedEmbedding a + star (C.distinguishedEmbedding a) := by
  have hd : C.distinguishedEmbedding.comp (algebraMap L K) = τ₀ :=
    C.distinguishedEmbedding_comp
  have hn : 1 ≤ n := by have := C.rank_gt_one; omega
  have hne : ComplexEmbedding.conjugate C.distinguishedEmbedding ≠
      C.distinguishedEmbedding := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal C.distinguishedEmbedding
      (ComplexEmbedding.isReal_iff.mpr h)
  have hdc : (ComplexEmbedding.conjugate C.distinguishedEmbedding).comp
      (algebraMap L K) ≠ τ₀ := by
    intro h
    have he : ComplexEmbedding.conjugate τ₀ = τ₀ := by
      rw [← hd, ← ComplexEmbedding.conjugate_comp]
      exact h.trans hd.symm
    exact IsTotallyComplex.complexEmbedding_not_isReal τ₀
      (ComplexEmbedding.isReal_iff.mpr he)
  have hm (i : K →+* ℂ) :
      (D.realHodgeFunction C i : ℂ) * i a =
        (if i.comp (algebraMap L K) = τ₀ then (n : ℂ) * i a else 0) -
          (if i = C.distinguishedEmbedding then i a else 0) +
          (if i = ComplexEmbedding.conjugate C.distinguishedEmbedding then i a else 0) := by
    rw [D.realHodgeFunction_eq, C.hodgeFunction_eq_harris]
    by_cases hi : i = C.distinguishedEmbedding
    · subst i
      simp [hd, Ne.symm hne, Nat.cast_sub hn]
      ring
    · by_cases hic : i = ComplexEmbedding.conjugate C.distinguishedEmbedding
      · subst i
        simp only [ite_eq_right hi, ite_true, ite_eq_right hdc, Nat.cast_one, one_mul,
          sub_zero, zero_add]
      · simp [hi, hic]
  simp_rw [hm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show (∑ i : K →+* ℂ,
    if i.comp (algebraMap L K) = τ₀ then (n : ℂ) * i a else 0) =
      (n : ℂ) * ∑ i : K →+* ℂ,
        if i.comp (algebraMap L K) = τ₀ then i a else 0 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp]
  rw [HarrisTaylor.sum_embeddings_inducing_eq_trace]
  rfl

/-- The actual central Hodge trace is the conjugated Harris–Taylor arithmetic value. -/
theorem trace_kottwitzHodgeAction_center_harrisTaylor (a : K) :
    LinearMap.trace ℂ (D.kottwitzHodgeModule C)
      (D.kottwitzHodgeAction C
        ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] algebraMap K A a))) =
      C.distinguishedEmbedding
        (cmConjugation E K (HarrisTaylor.lieTraceValue L K n a)) := by
  have ht : _root_.Algebra.trace L K ((n : K) ^ 2 * a) =
      (n : L) ^ 2 * _root_.Algebra.trace L K a := by
    have hna : (n : K) ^ 2 * a = (n : L) ^ 2 • a := by
      rw [_root_.Algebra.smul_def, map_pow, map_natCast]
    rw [hna, map_smul, smul_eq_mul]
  have hres (b : L) :
      C.distinguishedEmbedding (algebraMap L K b) = τ₀ b :=
    RingHom.congr_fun C.distinguishedEmbedding_comp b
  rw [D.trace_kottwitzHodgeAction_center C hΦ,
    D.sum_realHodgeFunction_mul_embedding C, embedding_cmConjugation]
  simp only [HarrisTaylor.lieTraceValue, ht, map_add, map_sub, map_mul, map_pow,
    map_natCast, hres, IsCMField.complexEmbedding_complexConj,
    starRingEnd_apply, star_add, star_sub, star_mul, star_pow, star_natCast, star_star]
  ring

/-- The Harris–Taylor normalization explicitly conjugates the original reflex scalar map. -/
def harrisTaylorReflexToCM : D.kottwitzCocharacterReflexField C →ₐ[ℚ] K :=
  (cmConjugation E K).toRingHom.toRatAlgHom.comp (D.harrisReflexToCM C)

omit [IsCMField K] in
/-- The normalized scalar map realizes the conjugate of the given complex inclusion. -/
@[simp] theorem distinguishedEmbedding_harrisTaylorReflexToCM
    (t : D.kottwitzCocharacterReflexField C) :
    C.distinguishedEmbedding (D.harrisTaylorReflexToCM C t) = star (t : ℂ) := by
  change C.distinguishedEmbedding (cmConjugation E K (D.harrisReflexToCM C t)) = _
  rw [embedding_cmConjugation, D.distinguishedEmbedding_harrisReflexToCM C]

omit [IsCMField K] in
/-- The normalized map sends a conjugate distinguished value back to the original CM value. -/
theorem harrisTaylorReflexToCM_of_complex_eq
    (t : D.kottwitzCocharacterReflexField C) (b : K)
    (h : (t : ℂ) = C.distinguishedEmbedding (cmConjugation E K b)) :
    D.harrisTaylorReflexToCM C t = b := by
  apply C.distinguishedEmbedding.injective
  rw [D.distinguishedEmbedding_harrisTaylorReflexToCM C, h,
    embedding_cmConjugation, star_star]

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-- The normalized scheme map from the source CM base to the cocharacter reflex base. -/
def harrisTaylorCMToReflexBase :
    Spec (.of K) ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)) :=
  Spec.map (CommRingCat.ofHom (D.harrisTaylorReflexToCM C).toRingHom)

omit [IsCMField K] in
/-- The normalized complex point induces the conjugate complex inclusion. -/
theorem harrisTaylorCMToReflexBase_complex :
    Spec.map (CommRingCat.ofHom C.distinguishedEmbedding) ≫
        D.harrisTaylorCMToReflexBase C =
      Spec.map (CommRingCat.ofHom ((starRingEnd ℂ).comp
        (D.kottwitzCocharacterReflexField C).val.toRingHom)) := by
  unfold harrisTaylorCMToReflexBase
  rw [← Spec.map_comp]
  congr 1
  ext t
  exact D.distinguishedEmbedding_harrisTaylorReflexToCM C t

variable {S T : Scheme.{0}} (p : S ⟶ Spec (.of K))

/-- The normalized reflex structure on an actual CM-base scheme. -/
def harrisTaylorReflexStructure :
    S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)) :=
  p ≫ D.harrisTaylorCMToReflexBase C

omit [IsCMField K] in
/-- The constructed normalized reflex structure commutes with arbitrary base change. -/
theorem harrisTaylorReflexStructure_comp (f : T ⟶ S) :
    D.harrisTaylorReflexStructure C (f ≫ p) =
      f ≫ D.harrisTaylorReflexStructure C p :=
  Category.assoc f p (D.harrisTaylorCMToReflexBase C)

omit [IsCMField K] in
/-- Normalized reflex sections use the displayed conjugated scalar homomorphism. -/
theorem secHom_harrisTaylorReflexStructure (U : S.Opens) :
    secHom (D.harrisTaylorReflexStructure C p) U =
      CommRingCat.ofHom (D.harrisTaylorReflexToCM C).toRingHom ≫ secHom p U :=
  secHom_postcomp_specMap _ p U

omit [IsCMField K] in
/-- The actual reflex determinant sections use the normalized coefficients through `p`. -/
theorem harrisReflexSectionDeterminant_harrisTaylor_CM
    {ι : Type} [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
    (U : S.Opens) :
    D.harrisReflexSectionDeterminant C hΦ
        (D.harrisTaylorReflexStructure C p) a U =
      MvPolynomial.map (secHom p U).hom
        (D.kottwitzReflexDeterminantBaseChange C hΦ (fun i => (a i : A))
          (D.harrisTaylorReflexToCM C).toRingHom) := by
  unfold harrisReflexSectionDeterminant kottwitzReflexDeterminantBaseChange
  rw [D.secHom_harrisTaylorReflexStructure C p, MvPolynomial.map_map]
  rfl

end Langlands.Shimura.CentralSimpleUnitaryData
