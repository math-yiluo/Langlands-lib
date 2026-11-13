import Langlands.HarmonicAnalysis.Distribution.RenardCompletionActions
import Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroupProof
import Langlands.Representation.Hecke.LocalUnitsProof

/-! # Renard II.3.13: the completed Hecke comparison -/

noncomputable section

open MeasureTheory
open Langlands.Algebra

namespace Langlands.HarmonicAnalysis.Distribution.RenardCompletion

universe uG

section Construction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-! ### Local units and fixed tests -/

/-- The Hecke algebra is idempotented, with normalized compact-open indicators
as two-sided local units. -/
theorem heckeAlgebra_isIdempotented : IsIdempotented (Hecke.HeckeAlgebra μ) := by
  intro s
  obtain ⟨K, hK, _, hi, hs⟩ :=
    Hecke.HeckeAlgebra.finiteFamilyLocalUnits G μ s (⊤ : OpenSubgroup G)
  refine ⟨⟨Hecke.HeckeAlgebra.normalizedIndicator μ K hK, hi⟩, ?_⟩
  intro a ha
  change Hecke.HeckeAlgebra.normalizedIndicator μ K hK * a *
    Hecke.HeckeAlgebra.normalizedIndicator μ K hK = a
  rw [(hs a ha).1, (hs a ha).2]

/-- Every Hecke element has an idempotent left local unit. -/
theorem exists_leftUnit (h : Hecke.HeckeAlgebra μ) :
    ∃ e : Idempotent (Hecke.HeckeAlgebra μ), (e : Hecke.HeckeAlgebra μ) * h = h := by
  obtain ⟨e, he⟩ :=
    (IsIdempotented.iff_two_sided_local_units.mp (heckeAlgebra_isIdempotented μ)) {h}
  exact ⟨e, (he h (Finset.mem_singleton_self h)).1⟩

/-- A Hecke element `e` fixes a test `f` under the test operator `f ↦ f * ě`
transposed by the full right action. -/
def Fixes (e : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G) : Prop :=
  Hecke.TestFunction.convolution μ f
    (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ e)) = f

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem rightHeckeConvolution_apply_of_fixes (V : Distribution G)
    {e : Hecke.HeckeAlgebra μ} {f : SchwartzBruhat G} (hf : Fixes μ e f) :
    rightHeckeConvolution μ V e f = V f :=
  congrArg V hf

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem fixes_of_mul_inversion {e : Hecke.HeckeAlgebra μ} {f : SchwartzBruhat G}
    (he : e * (Hecke.HeckeAlgebra.toTestFunction μ).symm (Hecke.TestFunction.inversion f) =
      (Hecke.HeckeAlgebra.toTestFunction μ).symm (Hecke.TestFunction.inversion f)) :
    Fixes μ e f := by
  have h : Hecke.TestFunction.inversion (Hecke.TestFunction.convolution μ
      (Hecke.HeckeAlgebra.toTestFunction μ e) (Hecke.TestFunction.inversion f)) =
      Hecke.TestFunction.inversion (Hecke.TestFunction.inversion f) :=
    congrArg (fun k : Hecke.HeckeAlgebra μ =>
      Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ k)) he
  rw [inversion_convolution, Hecke.TestFunction.inversion_inversion] at h
  exact h

/-- Every test is fixed by some idempotent of the Hecke algebra. -/
theorem exists_fixes (f : SchwartzBruhat G) :
    ∃ e : Idempotent (Hecke.HeckeAlgebra μ), Fixes μ (e : Hecke.HeckeAlgebra μ) f := by
  obtain ⟨e, he⟩ := exists_leftUnit μ ((Hecke.HeckeAlgebra.toTestFunction μ).symm
    (Hecke.TestFunction.inversion f))
  exact ⟨e, fixes_of_mul_inversion μ he⟩

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- Fixing a test is inherited by larger idempotents. -/
theorem Fixes.mono {e e' : Idempotent (Hecke.HeckeAlgebra μ)} (hle : e ≤ e')
    {f : SchwartzBruhat G} (hf : Fixes μ (e : Hecke.HeckeAlgebra μ) f) :
    Fixes μ (e' : Hecke.HeckeAlgebra μ) f := by
  have hmul : Hecke.TestFunction.convolution μ
      (Hecke.HeckeAlgebra.toTestFunction μ (e' : Hecke.HeckeAlgebra μ))
      (Hecke.HeckeAlgebra.toTestFunction μ (e : Hecke.HeckeAlgebra μ)) =
      Hecke.HeckeAlgebra.toTestFunction μ (e : Hecke.HeckeAlgebra μ) :=
    ((Idempotent.le_iff_mul e e').mp hle).1
  unfold Fixes at hf ⊢
  calc Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion
          (Hecke.HeckeAlgebra.toTestFunction μ (e' : Hecke.HeckeAlgebra μ)))
      = Hecke.TestFunction.convolution μ (Hecke.TestFunction.convolution μ f
          (Hecke.TestFunction.inversion
            (Hecke.HeckeAlgebra.toTestFunction μ (e : Hecke.HeckeAlgebra μ))))
          (Hecke.TestFunction.inversion
            (Hecke.HeckeAlgebra.toTestFunction μ (e' : Hecke.HeckeAlgebra μ))) := by
        rw [hf]
    _ = Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion
          (Hecke.TestFunction.convolution μ
            (Hecke.HeckeAlgebra.toTestFunction μ (e' : Hecke.HeckeAlgebra μ))
            (Hecke.HeckeAlgebra.toTestFunction μ (e : Hecke.HeckeAlgebra μ)))) :=
        rightTest_assoc μ _ _ _
    _ = f := by rw [hmul, hf]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem Fixes.add {e : Hecke.HeckeAlgebra μ} {f g : SchwartzBruhat G}
    (hf : Fixes μ e f) (hg : Fixes μ e g) : Fixes μ e (f + g) := by
  unfold Fixes at *
  rw [Hecke.TestFunction.convolution_add_left, hf, hg]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [BorelSpace G]
  [μ.IsHaarMeasure] in
theorem Fixes.smul {e : Hecke.HeckeAlgebra μ} {f : SchwartzBruhat G}
    (hf : Fixes μ e f) (c : ℂ) : Fixes μ e (c • f) := by
  unfold Fixes at *
  rw [Hecke.TestFunction.convolution_smul_left, hf]

/-- Two tests have a common fixing idempotent. -/
theorem exists_fixes_two (f g : SchwartzBruhat G) :
    ∃ e : Idempotent (Hecke.HeckeAlgebra μ),
      Fixes μ (e : Hecke.HeckeAlgebra μ) f ∧ Fixes μ (e : Hecke.HeckeAlgebra μ) g := by
  classical
  obtain ⟨e₁, h₁⟩ := exists_fixes μ f
  obtain ⟨e₂, h₂⟩ := exists_fixes μ g
  obtain ⟨e, he⟩ := (heckeAlgebra_isIdempotented μ).finite_upper_bound {e₁, e₂}
  exact ⟨e, Fixes.mono μ (he e₁ (by simp)) h₁, Fixes.mono μ (he e₂ (by simp)) h₂⟩

/-- A distribution is determined by its full right actions of Hecke idempotents. -/
theorem distribution_ext_of_idempotents {V W : Distribution G}
    (h : ∀ e : Idempotent (Hecke.HeckeAlgebra μ),
      rightHeckeConvolution μ V (e : Hecke.HeckeAlgebra μ) =
        rightHeckeConvolution μ W (e : Hecke.HeckeAlgebra μ)) : V = W := by
  ext f
  obtain ⟨e, he⟩ := exists_fixes μ f
  calc V f = rightHeckeConvolution μ V (e : Hecke.HeckeAlgebra μ) f :=
        (rightHeckeConvolution_apply_of_fixes μ V he).symm
    _ = rightHeckeConvolution μ W (e : Hecke.HeckeAlgebra μ) f := by rw [h e]
    _ = W f := rightHeckeConvolution_apply_of_fixes μ W he

/-! ### Fixed tests from the hypotheses of the source formulas -/

omit [MeasurableSpace G] [BorelSpace G] in
/-- A test fixed by right convolution with `e_K` is right `K`-invariant. -/
theorem rightInvariant_of_rightConvolveTest (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G)
    (hf : rightConvolveTest f (compactSubgroupHaar K.toSubgroup hK : Distribution G) =
      (f : G → ℂ)) :
    ∀ k : K, ∀ x, f (x * (k : G)) = f x := by
  have key : ∀ x, subgroupIntegral K.toSubgroup hK (fun y => f (x * y⁻¹)) = f x := by
    intro x
    have h1 : rightConvolveTest f (compactSubgroupHaar K.toSubgroup hK : Distribution G) x =
        subgroupIntegral K.toSubgroup hK (fun y => f (x * y⁻¹)) := by
      change subgroupIntegral K.toSubgroup hK (Hecke.TestFunction.rightTranslate x⁻¹
        (Hecke.TestFunction.inversion f) : G → ℂ) = _
      apply subgroupIntegral_congr
      intro y _
      simp only [Hecke.TestFunction.rightTranslate_apply, Hecke.TestFunction.inversion_apply,
        mul_inv_rev, inv_inv]
    rw [← h1]
    exact congrFun hf x
  intro k x
  calc f (x * k) = subgroupIntegral K.toSubgroup hK (fun y => f (x * k * y⁻¹)) :=
        (key (x * k)).symm
    _ = subgroupIntegral K.toSubgroup hK
          (fun y => (fun z => f (x * z⁻¹)) (y * (k : G)⁻¹)) := by
        apply subgroupIntegral_congr
        intro y _
        simp only [mul_inv_rev, inv_inv, mul_assoc]
    _ = subgroupIntegral K.toSubgroup hK (fun z => f (x * z⁻¹)) :=
        subgroupIntegral_mul_right K.toSubgroup hK (fun z => f (x * z⁻¹)) (inv_mem k.property)
    _ = f x := key x

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- `e_K` fixes every right `K`-invariant test. -/
theorem fixes_normalizedIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) (hf : ∀ k : K, ∀ x, f (x * (k : G)) = f x) :
    Fixes μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) f := by
  classical
  have hinv : Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) =
      Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) := by
    ext x
    rw [Hecke.TestFunction.inversion_apply]
    change Hecke.HeckeAlgebra.normalizedIndicator μ K hK x⁻¹ =
      Hecke.HeckeAlgebra.normalizedIndicator μ K hK x
    simp only [Hecke.HeckeAlgebra.normalizedIndicator_apply]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [SetLike.mem_coe, inv_mem_iff]
  unfold Fixes
  rw [hinv]
  exact Hecke.HeckeAlgebra.mul_normalizedIndicator_of_rightInvariant μ K hK
    ((Hecke.HeckeAlgebra.toTestFunction μ).symm f) hf

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- The hypotheses of the inverse formula give a fixed test. -/
theorem fixes_of_rightConvolveTest (e : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G)
    (hfix : rightConvolveTest f (heckeDistribution μ e) = (f : G → ℂ))
    (hinv : GroupAction.inversionDistributions (heckeDistribution μ e) =
      heckeDistribution μ e) :
    Fixes μ e f := by
  unfold Fixes
  ext x
  rw [convolution_inversion_apply, ← congrFun hfix x]
  have h1 : rightConvolveTest f (heckeDistribution μ e) x =
      GroupAction.inversionDistributions (heckeDistribution μ e)
        (Hecke.TestFunction.leftTranslate x⁻¹ f) := by
    rw [GroupAction.inversionDistributions_apply]
    unfold rightConvolveTest
    congr 1
    ext y
    simp only [GroupAction.inversionTests_apply, Hecke.TestFunction.leftTranslate_apply,
      Hecke.TestFunction.rightTranslate_apply, mul_inv_rev, inv_inv]
  rw [h1, hinv, heckeDistribution_apply]
  congr 1
  funext y
  rw [Hecke.TestFunction.leftTranslate_apply, inv_inv, mul_comm]
  rfl

/-! ### Coordinates of right essentially compact distributions -/

/-- The Hecke element whose density is `T*h`. -/
def coord (T : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    Hecke.HeckeAlgebra μ :=
  Classical.choose (exists_heckeDistribution_eq μ T.property h)

theorem coord_spec (T : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    heckeDistribution μ (coord μ T h) = rightHeckeConvolution μ (T : Distribution G) h :=
  Classical.choose_spec (exists_heckeDistribution_eq μ T.property h)

theorem coord_eq {T : rightEssentiallyCompact μ} {h k : Hecke.HeckeAlgebra μ}
    (hk : heckeDistribution μ k = rightHeckeConvolution μ (T : Distribution G) h) :
    coord μ T h = k :=
  heckeDistribution_injective μ ((coord_spec μ T h).trans hk.symm)

theorem coord_mul (T : rightEssentiallyCompact μ) (h k : Hecke.HeckeAlgebra μ) :
    coord μ T (h * k) = coord μ T h * k := by
  apply coord_eq
  rw [← rightHeckeConvolution_heckeDistribution, coord_spec, rightHeckeConvolution_mul]

theorem coord_add (T U : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    coord μ (T + U) h = coord μ T h + coord μ U h := by
  apply coord_eq
  rw [map_add, coord_spec, coord_spec, Submodule.coe_add]
  exact (map_add (rightHeckeOperator μ h) _ _).symm

theorem coord_smul (c : ℂ) (T : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    coord μ (c • T) h = c • coord μ T h := by
  apply coord_eq
  rw [map_smul, coord_spec, Submodule.coe_smul]
  exact (map_smul (rightHeckeOperator μ h) c _).symm

/-- The compatible family of coordinates of `T`. -/
def family (T : rightEssentiallyCompact μ) :
    IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ) :=
  ⟨fun e => coord μ T (e : Hecke.HeckeAlgebra μ), by
    constructor
    · intro e
      change coord μ T e * e = coord μ T e
      rw [← coord_mul, e.property.eq]
    · intro e f hef
      change coord μ T f * e = coord μ T e
      rw [← coord_mul, ((Idempotent.le_iff_mul e f).mp hef).1]⟩

@[simp] theorem family_val (T : rightEssentiallyCompact μ)
    (e : Idempotent (Hecke.HeckeAlgebra μ)) :
    (family μ T).val e = coord μ T (e : Hecke.HeckeAlgebra μ) := rfl

/-! ### The inverse: distributions from compatible families -/

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem heckeDistribution_val_of_fixes
    (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    {e g : Idempotent (Hecke.HeckeAlgebra μ)} (heg : e ≤ g) {f : SchwartzBruhat G}
    (hf : Fixes μ (e : Hecke.HeckeAlgebra μ) f) :
    heckeDistribution μ (a.val e) f = heckeDistribution μ (a.val g) f := by
  rw [← a.property.2 e g heg, ← rightHeckeConvolution_heckeDistribution]
  exact rightHeckeConvolution_apply_of_fixes μ _ hf

theorem heckeDistribution_val_eq_of_fixes
    (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    {e e' : Idempotent (Hecke.HeckeAlgebra μ)} {f : SchwartzBruhat G}
    (hf : Fixes μ (e : Hecke.HeckeAlgebra μ) f) (hf' : Fixes μ (e' : Hecke.HeckeAlgebra μ) f) :
    heckeDistribution μ (a.val e) f = heckeDistribution μ (a.val e') f := by
  classical
  obtain ⟨g, hg⟩ := (heckeAlgebra_isIdempotented μ).finite_upper_bound {e, e'}
  rw [heckeDistribution_val_of_fixes μ a (hg e (by simp)) hf,
    heckeDistribution_val_of_fixes μ a (hg e' (by simp)) hf']

/-- The value `(a_e)(f)` for a chosen idempotent `e` fixing `f`. -/
def invDistFun (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)) (f : SchwartzBruhat G) :
    ℂ :=
  heckeDistribution μ (a.val (Classical.choose (exists_fixes μ f))) f

/-- The distribution with `f ↦ (a_e)(f)` for any idempotent `e` fixing `f`. -/
def invDist (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)) : Distribution G where
  toFun := invDistFun μ a
  map_add' f g := by
    obtain ⟨e, hef, heg⟩ := exists_fixes_two μ f g
    unfold invDistFun
    rw [heckeDistribution_val_eq_of_fixes μ a
        (Classical.choose_spec (exists_fixes μ (f + g))) (hef.add μ heg),
      heckeDistribution_val_eq_of_fixes μ a (Classical.choose_spec (exists_fixes μ f)) hef,
      heckeDistribution_val_eq_of_fixes μ a (Classical.choose_spec (exists_fixes μ g)) heg,
      map_add]
  map_smul' c f := by
    obtain ⟨e, hef⟩ := exists_fixes μ f
    unfold invDistFun
    rw [heckeDistribution_val_eq_of_fixes μ a
        (Classical.choose_spec (exists_fixes μ (c • f))) (hef.smul μ c),
      heckeDistribution_val_eq_of_fixes μ a (Classical.choose_spec (exists_fixes μ f)) hef,
      map_smul]
    rfl

theorem invDist_apply (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    (f : SchwartzBruhat G) : invDist μ a f = invDistFun μ a f := rfl

theorem invDist_apply_of_fixes (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    {e : Idempotent (Hecke.HeckeAlgebra μ)} {f : SchwartzBruhat G}
    (hf : Fixes μ (e : Hecke.HeckeAlgebra μ) f) :
    invDist μ a f = heckeDistribution μ (a.val e) f := by
  rw [invDist_apply]
  unfold invDistFun
  exact heckeDistribution_val_eq_of_fixes μ a (Classical.choose_spec (exists_fixes μ f)) hf

theorem rightHeckeConvolution_invDist (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    {e : Idempotent (Hecke.HeckeAlgebra μ)} {h : Hecke.HeckeAlgebra μ}
    (he : (e : Hecke.HeckeAlgebra μ) * h = h) :
    rightHeckeConvolution μ (invDist μ a) h = heckeDistribution μ (a.val e * h) := by
  ext f
  have hfix : Fixes μ (e : Hecke.HeckeAlgebra μ) (Hecke.TestFunction.convolution μ f
      (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h))) := by
    unfold Fixes
    rw [rightTest_assoc]
    exact congrArg (fun k : Hecke.HeckeAlgebra μ => Hecke.TestFunction.convolution μ f
      (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ k))) he
  rw [rightHeckeConvolution_apply, invDist_apply_of_fixes μ a hfix,
    ← rightHeckeConvolution_heckeDistribution, rightHeckeConvolution_apply]

theorem invDist_mem (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)) :
    invDist μ a ∈ rightEssentiallyCompact μ := by
  intro h
  obtain ⟨e, he⟩ := exists_leftUnit μ h
  change rightHeckeConvolution μ (invDist μ a) h ∈ compactlySupported
  rw [rightHeckeConvolution_invDist μ a he]
  exact RenardHaar.testDensity_compactlySupported μ _

theorem coord_invDist (a : IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    (e : Idempotent (Hecke.HeckeAlgebra μ)) :
    coord μ ⟨invDist μ a, invDist_mem μ a⟩ (e : Hecke.HeckeAlgebra μ) = a.val e := by
  apply coord_eq
  show heckeDistribution μ (a.val e) = rightHeckeConvolution μ (invDist μ a) e
  rw [rightHeckeConvolution_invDist μ a e.property.eq, a.property.1 e]

/-- The comparison of right essentially compact distributions with compatible
families of Hecke coordinates. -/
def comparison :
    rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ) where
  toFun := family μ
  invFun a := ⟨invDist μ a, invDist_mem μ a⟩
  left_inv T := by
    apply Subtype.ext
    ext f
    obtain ⟨e, he⟩ := exists_fixes μ f
    change invDist μ (family μ T) f = (T : Distribution G) f
    rw [invDist_apply_of_fixes μ _ he, family_val, coord_spec,
      rightHeckeConvolution_apply_of_fixes μ _ he]
  right_inv a := by
    apply Subtype.ext
    funext e
    exact coord_invDist μ a e
  map_add' T U := by
    apply Subtype.ext
    funext e
    exact coord_add μ T U e

theorem comparison_val (T : rightEssentiallyCompact μ)
    (e : Idempotent (Hecke.HeckeAlgebra μ)) :
    (comparison μ T).val e = coord μ T (e : Hecke.HeckeAlgebra μ) := rfl

theorem comparison_smul (c : ℂ) (T : rightEssentiallyCompact μ)
    (e : Idempotent (Hecke.HeckeAlgebra μ)) :
    (comparison μ (c • T)).val e = c • (comparison μ T).val e :=
  coord_smul μ c T e

/-! ### The product -/

/-- The product transported from the source's product of compatible families. -/
def productFun (T U : rightEssentiallyCompact μ) : rightEssentiallyCompact μ :=
  (comparison μ).symm (IdempotentedRingRightLimit.product (heckeAlgebra_isIdempotented μ)
    (comparison μ T) (comparison μ U))

theorem comparison_productFun (T U : rightEssentiallyCompact μ) :
    comparison μ (productFun μ T U) =
      IdempotentedRingRightLimit.product (heckeAlgebra_isIdempotented μ)
        (comparison μ T) (comparison μ U) :=
  (comparison μ).apply_symm_apply _

theorem productFun_add_left (T T' U : rightEssentiallyCompact μ) :
    productFun μ (T + T') U = productFun μ T U + productFun μ T' U := by
  apply (comparison μ).injective
  rw [map_add, comparison_productFun, comparison_productFun, comparison_productFun, map_add,
    IdempotentedRingRightLimit.add_product]

theorem productFun_add_right (T U U' : rightEssentiallyCompact μ) :
    productFun μ T (U + U') = productFun μ T U + productFun μ T U' := by
  apply (comparison μ).injective
  rw [map_add, comparison_productFun, comparison_productFun, comparison_productFun, map_add,
    IdempotentedRingRightLimit.product_add]

theorem productFun_smul_left (c : ℂ) (T U : rightEssentiallyCompact μ) :
    productFun μ (c • T) U = c • productFun μ T U := by
  apply (comparison μ).injective
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := exists_leftUnit μ ((comparison μ U).val e)
  rw [comparison_smul, comparison_productFun, comparison_productFun,
    IdempotentedRingRightLimit.product_val _ _ _ e f hf,
    IdempotentedRingRightLimit.product_val _ _ _ e f hf, comparison_smul, smul_mul_assoc]

theorem productFun_smul_right (c : ℂ) (T U : rightEssentiallyCompact μ) :
    productFun μ T (c • U) = c • productFun μ T U := by
  apply (comparison μ).injective
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := exists_leftUnit μ ((comparison μ U).val e)
  have hf' : (f : Hecke.HeckeAlgebra μ) * (comparison μ (c • U)).val e =
      (comparison μ (c • U)).val e := by
    rw [comparison_smul, mul_smul_comm, hf]
  change (comparison μ (productFun μ T (c • U))).val e =
    (comparison μ (c • productFun μ T U)).val e
  rw [comparison_smul, comparison_productFun, comparison_productFun,
    IdempotentedRingRightLimit.product_val _ _ _ e f hf',
    IdempotentedRingRightLimit.product_val _ _ _ e f hf, comparison_smul, mul_smul_comm]

/-- The bilinear product on right essentially compact distributions. -/
def essentialProduct :
    rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ :=
  LinearMap.mk₂ ℂ (productFun μ) (productFun_add_left μ) (productFun_smul_left μ)
    (productFun_add_right μ) (productFun_smul_right μ)

theorem comparison_essentialProduct (T U : rightEssentiallyCompact μ) :
    comparison μ (essentialProduct μ T U) =
      IdempotentedRingRightLimit.product (heckeAlgebra_isIdempotented μ)
        (comparison μ T) (comparison μ U) :=
  comparison_productFun μ T U

/-- The coordinates of a product: `(T*U)*h = T*(U*h)`, in Hecke coordinates. -/
theorem coord_essentialProduct (T U : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    coord μ (essentialProduct μ T U) h = coord μ T (coord μ U h) := by
  obtain ⟨e₀, he₀⟩ := exists_leftUnit μ h
  obtain ⟨f, hf⟩ := exists_leftUnit μ (coord μ U e₀)
  have hP : (comparison μ (essentialProduct μ T U)).val e₀ =
      coord μ T f * coord μ U e₀ := by
    rw [comparison_essentialProduct]
    exact IdempotentedRingRightLimit.product_val _ _ _ e₀ f hf
  calc coord μ (essentialProduct μ T U) h
      = coord μ (essentialProduct μ T U) (e₀ * h) := by rw [he₀]
    _ = coord μ T f * coord μ U e₀ * h := by
        rw [coord_mul]
        exact congrArg (· * h) hP
    _ = coord μ T (f * (coord μ U e₀ * h)) := by rw [coord_mul, mul_assoc]
    _ = coord μ T (coord μ U h) := by rw [← mul_assoc, hf, ← coord_mul, he₀]

theorem rightHeckeConvolution_essentialProduct (T U : rightEssentiallyCompact μ)
    (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (essentialProduct μ T U : Distribution G) h =
      rightHeckeConvolution μ (T : Distribution G) (coord μ U h) := by
  rw [← coord_spec, coord_essentialProduct, coord_spec]

/-! ### Distinguished elements -/

/-- The Dirac distribution at the identity, as a right essentially compact element. -/
def diracElement : rightEssentiallyCompact μ :=
  ⟨dirac 1, dirac_one_mem_rightEssentiallyCompact μ⟩

/-- A Hecke density, as a right essentially compact element. -/
def heckeElement (h : Hecke.HeckeAlgebra μ) : rightEssentiallyCompact μ :=
  ⟨heckeDistribution μ h, heckeDistribution_mem_rightEssentiallyCompact μ h⟩

theorem coord_diracElement (h : Hecke.HeckeAlgebra μ) : coord μ (diracElement μ) h = h :=
  coord_eq μ (rightHeckeConvolution_dirac_one μ h).symm

theorem coord_heckeElement (h k : Hecke.HeckeAlgebra μ) :
    coord μ (heckeElement μ h) k = h * k :=
  coord_eq μ (rightHeckeConvolution_heckeDistribution μ h k).symm

theorem comparison_diracElement :
    comparison μ (diracElement μ) = IdempotentedRingRightLimit.unit := by
  apply Subtype.ext
  funext e
  exact coord_diracElement μ e

theorem comparison_heckeElement (h : Hecke.HeckeAlgebra μ) :
    comparison μ (heckeElement μ h) = IdempotentedRingRightLimit.canonical h := by
  apply Subtype.ext
  funext e
  exact coord_heckeElement μ h e

/-! ### The specifications -/

theorem essentialProduct_algebraLaws :
    RenardEssentialProducts.AlgebraLaws μ (rightEssentiallyCompact μ) (essentialProduct μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T U V
    apply (comparison μ).injective
    simp only [comparison_essentialProduct, IdempotentedRingRightLimit.product_assoc]
  · refine ⟨diracElement μ, rfl, fun T => ⟨?_, ?_⟩⟩
    · apply (comparison μ).injective
      rw [comparison_essentialProduct, comparison_diracElement,
        IdempotentedRingRightLimit.unit_product]
    · apply (comparison μ).injective
      rw [comparison_essentialProduct, comparison_diracElement,
        IdempotentedRingRightLimit.product_unit]
  · intro T U
    let t : rightEssentiallyCompact μ := ⟨T, compact_mem_rightEssentiallyCompact μ T⟩
    let u : rightEssentiallyCompact μ := ⟨U, compact_mem_rightEssentiallyCompact μ U⟩
    refine ⟨t, u, rfl, rfl, ?_⟩
    apply distribution_ext_of_idempotents μ
    intro e
    have hU : (convolution U (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ
        (e : Hecke.HeckeAlgebra μ))) : Distribution G) =
        heckeDistribution μ (coord μ u e) := by
      rw [← rightHeckeConvolution_compact, coord_spec]
    have hU' : convolution U (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ
        (e : Hecke.HeckeAlgebra μ))) =
        compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ (coord μ u e)) :=
      Subtype.ext hU
    have h1 : rightHeckeConvolution μ (t : Distribution G) (coord μ u e) =
        rightHeckeConvolution μ (T : Distribution G) (coord μ u e) := rfl
    rw [rightHeckeConvolution_essentialProduct, h1, rightHeckeConvolution_compact,
      rightHeckeConvolution_compact, convolution_associative, hU']
  · intro T h
    refine ⟨heckeElement μ h, rfl, ?_, ?_⟩
    · apply distribution_ext_of_idempotents μ
      intro e
      rw [rightHeckeConvolution_essentialProduct, coord_heckeElement, rightHeckeConvolution_mul]
    · apply distribution_ext_of_idempotents μ
      intro e
      rw [rightHeckeConvolution_essentialProduct, ← leftHecke_rightHecke_comm,
        ← coord_spec μ T e, leftHeckeConvolution_heckeDistribution]
      exact rightHeckeConvolution_heckeDistribution μ h (coord μ T e)

theorem essentialProduct_rightSpecification :
    RenardEssentialProducts.RightProductSpecification μ (essentialProduct μ) := by
  refine ⟨essentialProduct_algebraLaws μ, ?_, ?_⟩
  · intro T U f K hK hf
    refine ⟨coord μ U (Hecke.HeckeAlgebra.normalizedIndicator μ K hK), coord_spec μ U _, ?_⟩
    have hfix : Fixes μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) f :=
      fixes_normalizedIndicator μ K hK f (rightInvariant_of_rightConvolveTest K hK f hf)
    rw [← rightHeckeConvolution_apply_of_fixes μ _ hfix,
      rightHeckeConvolution_essentialProduct]
  · intro T U h
    exact ⟨coord μ U h, coord_spec μ U h, rightHeckeConvolution_essentialProduct μ T U h⟩

theorem comparison_specification :
    ComparisonSpecification μ (heckeAlgebra_isIdempotented μ) (essentialProduct μ)
      (comparison μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T e
    exact coord_spec μ T e
  · intro c T e
    exact coord_smul μ c T e
  · intro T U
    exact comparison_essentialProduct μ T U
  · exact ⟨diracElement μ, rfl, comparison_diracElement μ⟩
  · intro h
    exact ⟨heckeElement μ h, rfl, comparison_heckeElement μ h⟩
  · intro a f e hfix hinv
    exact invDist_apply_of_fixes μ a (fixes_of_rightConvolveTest μ e f hfix hinv)

/-- Any comparison satisfying the first clause of the specification is `comparison`. -/
theorem eq_comparison
    (E : rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    (hE : ∀ (T : rightEssentiallyCompact μ) (e : Idempotent (Hecke.HeckeAlgebra μ)),
      heckeDistribution μ ((E T).val e) =
        rightHeckeConvolution μ (T : Distribution G) (e : Hecke.HeckeAlgebra μ)) :
    E = comparison μ := by
  apply AddEquiv.ext
  intro T
  apply Subtype.ext
  funext e
  exact (coord_eq μ (hE T e)).symm

end Construction

/-- II.3.13 Theorem: the right product exists, and the comparison with the
idempotented completion of the Hecke algebra exists and is unique. -/
theorem statements : Statements.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  refine ⟨heckeAlgebra_isIdempotented μ, essentialProduct μ,
    essentialProduct_rightSpecification μ, comparison μ, comparison_specification μ, ?_⟩
  intro E hE
  exact eq_comparison μ E hE.1

end Langlands.HarmonicAnalysis.Distribution.RenardCompletion
