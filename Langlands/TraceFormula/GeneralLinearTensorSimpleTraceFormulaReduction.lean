import Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaStatement
import Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingStatement
import Langlands.Analysis.Local.CompactQuotientSmoothTraceClassReduction
import Langlands.Analysis.OperatorTraceProof
import Langlands.TraceFormula.CompactSmoothAdelicGLTestConvolution
import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaStatement
import Langlands.TraceFormula.GeneralLinearSimpleTraceExpansionMerge

/-!
# The simple trace formula on sums of tensor test functions, from the simple trace formula

* `generalLinearTensorSimpleTracePieces_of_simpleTraceFormula` proves
  `GeneralLinearTensorSimpleTracePiecesStatement` from `GeneralLinearSimpleTraceFormulaStatement`
  and `GeneralLinearRadicalIntegralVanishingStatement`, through the factorization of tensor tests
  that keeps the finite component (`CompactSmoothAdelicGLTestConvolution`).
* `generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula` proves
  `GeneralLinearTensorSimpleTraceFormulaStatement` from the same two statements: the pieces are
  merged into one expansion by `generalLinearSimpleTraceExpansion_finsetSum`.

Also: `Langlands.Analysis.integratedIsometricAction_sum`,
`Langlands.Analysis.operatorTrace_finsetSum`,
`Langlands.Analysis.continuous_convolution_compactlySupported` and
`Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`.
-/
noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Filter
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals

namespace Langlands.Analysis

section Sums

variable {G : Type*} [Group G] [MeasurableSpace G]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ν₀ : Measure G) (π : G →* (E →L[ℂ] E))
  (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
  (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) ν₀)

/-- The integrated operator of a finite sum of integrable weights is the sum of the integrated operators. -/
theorem integratedIsometricAction_sum {Ix : Type*} [Fintype Ix] (f : Ix → G → ℂ)
    (hf : ∀ i, Integrable (f i) ν₀) (h : Integrable (∑ i, f i) ν₀) :
    integratedIsometricAction ν₀ π hπnorm hπmeas (∑ i, f i) h =
      ∑ i, integratedIsometricAction ν₀ π hπnorm hπmeas (f i) (hf i) := by
  ext x
  simp only [integratedIsometricAction_apply, sum_apply, Finset.sum_apply,
    Finset.sum_smul]
  exact integral_finsetSum _ fun i _ =>
    isometricActionIntegrand_integrable ν₀ π hπnorm hπmeas (f i) (hf i) x

end Sums

/-- A finite sum of trace-class operators is trace class, and its trace is the sum of the traces. -/
theorem operatorTrace_finsetSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {Ix : Type*} (s : Finset Ix) (A : Ix → E →L[ℂ] E)
    (hA : ∀ i ∈ s, IsTraceClass (A i)) :
    IsTraceClass (∑ i ∈ s, A i) ∧ operatorTrace (∑ i ∈ s, A i) = ∑ i ∈ s, operatorTrace (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isTraceClass_zero, operatorTrace_zero]
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have ha' := hA a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨isTraceClass_add _ _ ha' h1, by rw [operatorTrace_add _ _ ha' h1, h2]⟩

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

/-- The Haar convolution `g ↦ ∫ f₁(x) f₂(x⁻¹ g) dν₀(x)` of two compactly supported continuous
functions is continuous. -/
theorem continuous_convolution_compactlySupported (ν₀ : Measure G) [IsFiniteMeasureOnCompacts ν₀]
    (f₁ f₂ : C_c(G, ℂ)) : Continuous (fun g => ∫ x, f₁ x * f₂ (x⁻¹ * g) ∂ν₀) := by
  rw [← continuousOn_univ]
  refine continuousOn_integral_of_compact_support f₁.hasCompactSupport ?_ ?_
  · exact ((f₁.continuous.comp continuous_snd).mul
      (f₂.continuous.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
  · intro p x _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

omit [IsTopologicalGroup G] [BorelSpace G] in
/-- The Haar convolution of two compactly supported continuous functions on a Hausdorff group
vanishes outside `supp f₁ · supp f₂`, so it has compact support. -/
theorem hasCompactSupport_convolution_compactlySupported [IsTopologicalGroup G] [T2Space G]
    (ν₀ : Measure G) (f₁ f₂ : C_c(G, ℂ)) :
    HasCompactSupport (fun g => ∫ x, f₁ x * f₂ (x⁻¹ * g) ∂ν₀) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (f₁.hasCompactSupport.isCompact.mul f₂.hasCompactSupport.isCompact) fun g hg => ?_
  by_contra hK
  apply hg
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  by_cases h₁ : f₁ x = 0
  · simp [h₁]
  · have h₂ : f₂ (x⁻¹ * g) = 0 := by
      by_contra h₂
      exact hK ⟨x, subset_tsupport _ h₁, x⁻¹ * g, subset_tsupport _ h₂, by simp⟩
    simp [h₂]

end Convolution

end Langlands.Analysis

namespace Langlands.TraceFormula

open Langlands.GeneralLinear Langlands.Analysis

local instance generalLinearTensorReductionIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearTensorReductionSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

section Expansion

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant]
  (v : Langlands.Global.FinitePlace F)

/-- `f` is a finite sum of Haar convolutions `f₁ₖ ⋆ f₂ₖ` of compactly supported continuous functions on
`GL_n(𝔸_F)`, each of which satisfies the simple trace formula at `v`
(`GeneralLinearSimpleTraceExpansion`). -/
def GeneralLinearTraceExpansionSum (f : AdelicGroupPoints F GLₙ → ℂ) : Prop :=
  ∃ (N : ℕ) (f₁ f₂ : Fin N → C_c(AdelicGroupPoints F GLₙ, ℂ))
    (hk : ∀ k, Integrable (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g)
      ∂(Measure.haar : Measure (AdelicGroupPoints F GLₙ)))
      (Measure.haar : Measure (AdelicGroupPoints F GLₙ))),
    (∀ g, f g = ∑ k, ∫ x, f₁ k x * f₂ k (x⁻¹ * g)
      ∂(Measure.haar : Measure (AdelicGroupPoints F GLₙ))) ∧
    ∀ k, GeneralLinearSimpleTraceExpansion F n T i hi I e hc v
      (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂(Measure.haar : Measure (AdelicGroupPoints F GLₙ)))
      (hk k)

/-- `0` is an empty such sum. -/
theorem generalLinearTraceExpansionSum_zero :
    GeneralLinearTraceExpansionSum F n T i hi I e hc v 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun g => by simp, fun k => k.elim0⟩

/-- Such sums are closed under addition (concatenation of the pieces). -/
theorem GeneralLinearTraceExpansionSum.add {f₁ f₂ : AdelicGroupPoints F GLₙ → ℂ}
    (h₁ : GeneralLinearTraceExpansionSum F n T i hi I e hc v f₁)
    (h₂ : GeneralLinearTraceExpansionSum F n T i hi I e hc v f₂) :
    GeneralLinearTraceExpansionSum F n T i hi I e hc v (f₁ + f₂) := by
  obtain ⟨N₁, a₁, b₁, hk₁, he₁, hx₁⟩ := h₁
  obtain ⟨N₂, a₂, b₂, hk₂, he₂, hx₂⟩ := h₂
  refine ⟨N₁ + N₂, Fin.append a₁ a₂, Fin.append b₁ b₂, fun k => ?_, fun g => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simpa only [Fin.append_left] using hk₁ k
    · simpa only [Fin.append_right] using hk₂ k
  · rw [Fin.sum_univ_add, Pi.add_apply, he₁ g, he₂ g]
    simp only [Fin.append_left, Fin.append_right]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Fin.append_left]
      exact hx₁ k
    · simp only [Fin.append_right]
      exact hx₂ k

/-- Such sums are closed under finite sums. -/
theorem generalLinearTraceExpansionSum_finsetSum {Ix : Type*} (s : Finset Ix)
    {f : Ix → AdelicGroupPoints F GLₙ → ℂ}
    (hf : ∀ j ∈ s, GeneralLinearTraceExpansionSum F n T i hi I e hc v (f j)) :
    GeneralLinearTraceExpansionSum F n T i hi I e hc v (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using generalLinearTraceExpansionSum_zero F n T i hi I e hc v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add F n T i hi I e hc v
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end Expansion

/-- `GeneralLinearTensorSimpleTracePiecesStatement` follows from
`GeneralLinearSimpleTraceFormulaStatement` and `GeneralLinearRadicalIntegralVanishingStatement`.
Each tensor `aⱼ ⊗ bⱼ` is factored as `∑ᵢ (αᵢ ⊗ 1_K) ⋆ (α'ᵢ ⊗ bⱼ)`
(`CompactSmoothAdelicGLTest.exists_eq_sum_convolution_subgroupIndicator`), for the image of the
Haar measure of `GL_n(𝔸_F)`; every pair of factors satisfies the hypotheses of the simple trace
formula: both are tensor tests (Hilbert–Schmidt by assumption), the right factor has the vanishing
radical integrals because its finite component is `bⱼ`, and the support of the product lies over the
support of `bⱼ`, hence is regular elliptic at `v`. The pieces are then added. -/
theorem generalLinearTensorSimpleTracePieces_of_simpleTraceFormula
    (hTF : GeneralLinearSimpleTraceFormulaStatement.{u})
    (hRV : GeneralLinearRadicalIntegralVanishingStatement.{u}) :
    GeneralLinearTensorSimpleTracePiecesStatement.{u} := by
  intro F _ _ n hPD hG T i hi _ I _ e hc _ μG hHS m a b w hloc v hell f
  let _ : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  let _ : MeasurableSpace (InfiniteAdelicGL F n) := ArchimedeanGL.borelMeasurableSpace F n
  have : BorelSpace (InfiniteAdelicGL F n) := ArchimedeanGL.borelMeasurableSpace_borelSpace F n
  set φ := GeneralLinearGroupPoints.adelicHomeomorph F n
  have : (μG.map φ).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μG φ
  let pullCc : ArchimedeanGL.SmoothCompactKernel F n → CompactFiniteGLTest F n →
      C_c(AdelicGroupPoints F GLₙ, ℂ) := fun α β =>
    ⟨⟨fun g => adelicTestTensor F n α β (φ g),
      (CompactSmoothAdelicGLTest.continuous F n (CompactSmoothAdelicGLTest.tensor F n α β)).comp
        φ.continuous⟩,
      (CompactSmoothAdelicGLTest.hasCompactSupport F n
        (CompactSmoothAdelicGLTest.tensor F n α β)).comp_homeomorph φ.toHomeomorph⟩
  have hofFin : ∀ u : FiniteAdelicGL F n,
      AdelicGL.infinite F n (AdelicGL.ofFinite F n u) = 1 ∧
        AdelicGL.finite F n (AdelicGL.ofFinite F n u) = u := fun u =>
    ⟨AdelicGL.infinite_pair F n 1 u, AdelicGL.finite_pair F n 1 u⟩
  have key : ∀ j, GeneralLinearTraceExpansionSum F n T i hi I e hc v
      (fun g => adelicTestTensor F n (a j) (b j) (φ g)) := by
    intro j
    obtain ⟨K, hK, hKb, mj, α, α', hsupp, hsum⟩ :=
      CompactSmoothAdelicGLTest.exists_eq_sum_convolution_subgroupIndicator F n (μG.map φ)
        (a j) (b j) Filter.univ_mem
    set e₀ := CompactFiniteGLTest.subgroupIndicator F n K hK
    have hconv : ∀ l g, (∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG) =
        (∫ z, (α l).val.val z * (α' l).val.val (z⁻¹ * AdelicGL.infinite F n (φ g))
          ∂finiteSliceMeasure F n (μG.map φ) K) *
          (b j).val (AdelicGL.finite F n (φ g)) := by
      intro l g
      have h1 := Hecke.convolutionIntegral_comp_continuousMulEquiv φ μG
        (adelicTestTensor F n (α l) e₀) (adelicTestTensor F n (α' l) (b j)) g
      rw [Hecke.convolutionIntegral, Hecke.convolutionIntegral] at h1
      rw [← CompactSmoothAdelicGLTest.convolution_tensor_subgroupIndicator F n (μG.map φ) K hK
        (b j) hKb (α l) (α' l) (φ g)]
      exact h1
    have hsupp_conv : ∀ l, ∀ g ∈ tsupport (fun g =>
        ∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG),
        AdelicGL.finite F n (φ g) ∈ tsupport (b j).val := by
      intro l
      have hcl : IsClosed ((fun g => AdelicGL.finite F n (φ g)) ⁻¹' tsupport (b j).val) :=
        (isClosed_tsupport _).preimage ((AdelicGL.finite F n).continuous.comp φ.continuous)
      refine fun g hg => closure_minimal (fun g' hg' => ?_) hcl hg
      by_contra hb
      apply hg'
      change (∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g') ∂μG) = 0
      rw [hconv l g', image_eq_zero_of_notMem_tsupport hb, mul_zero]
    have hlocal : ∀ l, ∀ (p q : ℕ) (hpq : p + q = n), 0 < p → 0 < q →
        letI : MeasurableSpace (Matrix (Fin p) (Fin q) (FiniteCompletion F (w j))) := borel _
        ∀ ν : Measure (Matrix (Fin p) (Fin q) (FiniteCompletion F (w j))), ν.IsAddHaarMeasure →
          ∀ x y : AdelicGL F n,
            ∫ Z, adelicTestTensor F n (α' l) (b j) (x * AdelicGL.ofFinite F n
              (FiniteAdelicGL.localInclusion F n (w j) (blockUnipotent hpq Z)) * y) ∂ν = 0 := by
      intro l p q hpq hp hq ν hν x y
      have hZ : ∀ Z, adelicTestTensor F n (α' l) (b j) (x * AdelicGL.ofFinite F n
          (FiniteAdelicGL.localInclusion F n (w j) (blockUnipotent hpq Z)) * y) =
          (α' l).val.val (AdelicGL.infinite F n x * AdelicGL.infinite F n y) *
            (b j).val (AdelicGL.finite F n x *
              FiniteAdelicGL.localInclusion F n (w j) (blockUnipotent hpq Z) *
                AdelicGL.finite F n y) := by
        intro Z
        simp only [adelicTestTensor, ArchimedeanGL.kernelToContinuousMap_apply, map_mul,
          (hofFin _).1, (hofFin _).2, mul_one]
      simp_rw [hZ]
      rw [integral_const_mul, hloc j p q hpq hp hq ν hν, mul_zero]
    have hsupport : ∀ l, ∀ g ∈ tsupport (fun g =>
        ∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG),
        IsRegularElliptic (FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n (φ g))) := by
      intro l g hg
      have hy := hsupp_conv l g hg
      by_cases ha : ∃ x0, (a j).val.val x0 ≠ 0
      · obtain ⟨x0, hx0⟩ := ha
        have hpair : AdelicGL.pair F n x0 (AdelicGL.finite F n (φ g)) ∈
            tsupport (adelicTestTensor F n (a j) (b j)) := by
          have hcp : Continuous fun y' => AdelicGL.pair F n x0 y' :=
            (AdelicGL.continuous_pair F n).comp (continuous_const.prodMk continuous_id)
          refine closure_mono ?_ (image_closure_subset_closure_image hcp ⟨_, hy, rfl⟩)
          rintro _ ⟨y', hy', rfl⟩
          change adelicTestTensor F n (a j) (b j) (AdelicGL.pair F n x0 y') ≠ 0
          simp only [adelicTestTensor, ArchimedeanGL.kernelToContinuousMap_apply,
            AdelicGL.infinite_pair, AdelicGL.finite_pair]
          exact mul_ne_zero hx0 hy'
        have := hell j _ hpair
        rwa [AdelicGL.finite_pair] at this
      · exfalso
        have ha' : ∀ x0, (a j).val.val x0 = 0 := fun x0 => by_contra fun h => ha ⟨x0, h⟩
        have hta : tsupport (a j).val.val = ∅ := by
          rw [tsupport, Function.support_eq_empty_iff.2 (funext ha'), closure_empty]
        have hα' : ∀ z, (α' l).val.val z = 0 := fun z =>
          image_eq_zero_of_notMem_tsupport fun hz => by
            have := (hsupp l).2 hz
            rw [hta] at this
            exact this
        have hzero : (fun g => ∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG) = 0 := by
          funext g'
          change (∫ x, adelicTestTensor F n (α l) e₀ (φ x) *
            adelicTestTensor F n (α' l) (b j) (φ (x⁻¹ * g')) ∂μG) = 0
          simp [adelicTestTensor, ArchimedeanGL.kernelToContinuousMap_apply, hα']
        rw [hzero, tsupport_zero] at hg
        exact hg
    have hTFl : ∀ l, ∃ h : Integrable (fun g =>
        ∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG) μG,
        GeneralLinearSimpleTraceExpansion F n T i hi I e hc v
          (fun g => ∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG) h := by
      intro l
      exact hTF F n hPD hG T i hi I e hc (pullCc (α l) e₀) (pullCc (α' l) (b j))
        (fun h₁ => hHS (α l) e₀ h₁) (fun h₂ => hHS (α' l) (b j) h₂)
        (fun P x y => hRV F n hPD hG (w j) (adelicTestTensor F n (α' l) (b j))
          (CompactSmoothAdelicGLTest.continuous F n (CompactSmoothAdelicGLTest.tensor F n _ _))
          (CompactSmoothAdelicGLTest.hasCompactSupport F n (CompactSmoothAdelicGLTest.tensor F n _ _))
          (hlocal l) P x y)
        v (hsupport l)
    choose hk hexp using hTFl
    refine ⟨mj, fun l => pullCc (α l) e₀, fun l => pullCc (α' l) (b j), hk, fun g => ?_, hexp⟩
    change adelicTestTensor F n (a j) (b j) (φ g) =
      ∑ l, ∫ x, pullCc (α l) e₀ x * pullCc (α' l) (b j) (x⁻¹ * g) ∂μG
    rw [hsum (φ g)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 := Hecke.convolutionIntegral_comp_continuousMulEquiv φ μG
      (adelicTestTensor F n (α l) e₀) (adelicTestTensor F n (α' l) (b j)) g
    rw [Hecke.convolutionIntegral, Hecke.convolutionIntegral] at h1
    exact h1.symm
  have hsumf : GeneralLinearTraceExpansionSum F n T i hi I e hc v f := by
    have hfe : f = ∑ j, fun g => adelicTestTensor F n (a j) (b j) (φ g) := by
      funext g
      rw [Finset.sum_apply]
    rw [hfe]
    exact generalLinearTraceExpansionSum_finsetSum F n T i hi I e hc v Finset.univ fun j _ => key j
  obtain ⟨N, f₁, f₂, hk, hfeq, hexp⟩ := hsumf
  have hfconv : f = ∑ k, fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG := by
    funext g
    rw [hfeq g, Finset.sum_apply]
  have hI : Integrable f μG := by
    rw [hfconv]
    exact integrable_finsetSum' _ fun k _ => hk k
  have hR : haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f hI =
      ∑ k, haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG
        (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) (hk k) := by
    change integratedIsometricAction μG (haarQuotientL2BoundedRightAction F GLₙ T i hi I e hc)
        (norm_haarQuotientL2BoundedRightAction F GLₙ T i hi I e hc)
        (haarQuotientL2Orbit_aestronglyMeasurable F GLₙ T i hi I e hc μG) f hI =
      ∑ k, integratedIsometricAction μG (haarQuotientL2BoundedRightAction F GLₙ T i hi I e hc)
        (norm_haarQuotientL2BoundedRightAction F GLₙ T i hi I e hc)
        (haarQuotientL2Orbit_aestronglyMeasurable F GLₙ T i hi I e hc μG)
        (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) (hk k)
    rw [integratedIsometricAction_congr _ _ _ _ hfconv hI (hfconv ▸ hI),
      integratedIsometricAction_sum]
  have htc := operatorTrace_finsetSum (Finset.univ : Finset (Fin N)) (fun k =>
    haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG
      (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) (hk k)) fun k _ => by
    obtain ⟨h1, -⟩ := hexp k
    exact h1
  refine ⟨hI, ?_, N, f₁, f₂, hk, hfeq, hexp, ?_⟩
  · rw [hR]
    exact htc.1
  · rw [hR]
    exact htc.2

/-- `GeneralLinearTensorSimpleTraceFormulaStatement` follows from
`GeneralLinearSimpleTraceFormulaStatement` and `GeneralLinearRadicalIntegralVanishingStatement`.
`generalLinearTensorSimpleTracePieces_of_simpleTraceFormula` writes `f = ∑ₖ f₁ₖ ⋆ f₂ₖ` with
`R(f)` trace class, `tr R(f) = ∑ₖ tr R(f₁ₖ ⋆ f₂ₖ)` and every piece satisfying the simple trace
formula with its own representatives; the pieces are continuous with compact support
(`Langlands.Analysis.continuous_convolution_compactlySupported`,
`Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`), and
`generalLinearSimpleTraceExpansion_finsetSum` merges their expansions into one, by the invariance
of the orbital terms under change of representative within a class
(`exists_isCompatible_of_isTwistedConjugate`). -/
theorem generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula
    (hTF : GeneralLinearSimpleTraceFormulaStatement.{u})
    (hRV : GeneralLinearRadicalIntegralVanishingStatement.{u}) :
    GeneralLinearTensorSimpleTraceFormulaStatement.{u} := by
  intro F _ _ n hPD hG T i hi _ I _ e hc _ μG hHS m a b w hloc v hell f
  obtain ⟨h, htc, N, f₁, f₂, hk, hfeq, hexp, htr⟩ :=
    generalLinearTensorSimpleTracePieces_of_simpleTraceFormula hTF hRV F n hPD hG T i hi I e hc
      hHS m a b w hloc v hell
  exact ⟨h, generalLinearSimpleTraceExpansion_finsetSum F n T i hi I e hc v h
    (fun k g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG)
    (fun k => continuous_convolution_compactlySupported μG (f₁ k) (f₂ k))
    (fun k => hasCompactSupport_convolution_compactlySupported μG (f₁ k) (f₂ k))
    hk hfeq hexp htc htr⟩

end Langlands.TraceFormula
