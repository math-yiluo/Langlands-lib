import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingStatement
import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenCellIntegral

/-! # Proof of the unfolding of the generic coefficient

The generic coefficient `coeff ψ φ s` is the normalized integral over a fundamental domain of
`N₀(F)` in `N₀(𝔸)` of the Eisenstein series against the conjugate generic character. On the
half-plane of normal convergence, the Eisenstein sum splits over the cells of
`P(F) \ GL_N(F) / N₀(F)`; each cell unfolds, the non-open cells contribute zero, and the open cell
contributes `κ · openCellIntegral ψ φ s`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Set
open scoped NNReal ENNReal

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon LeftCosetSpace
open scoped CategoryTheory.MonObj

attribute [local instance] leviIntegralSchemeAffine leviIntegralSchemeSmooth
  radicalMatrixMeasurableSpace radicalMatrixBorelSpace

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ} {σ : ℝ}

omit [CompactSpace (AdeleQuotient F)] in
theorem genericChar_eq (ψ : AddChar (Adeles F) ℂ) (x : unipotentAdelic F (r + t + 2)) :
    genericChar ψ x = genericCharacter F (r + t + 1) ψ (fun _ => 1) x := by
  simp only [genericChar, genericCharacter, map_one, one_mul]
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem haarH_eq : haarH F r t =
    ((Measure.haar : Measure (unipotentAdelic F (r + t + 2))) (fd₀ F (r + t + 2)))⁻¹ •
      Measure.haar :=
  rfl

omit [CompactSpace (AdeleQuotient F)] in
/-- The global Whittaker coefficient at the identity of a continuous function on `GL_(n+1)(𝔸)`
left invariant under `GL_(n+1)(F)`, as an integral over a fundamental domain of `N_(n+1)(F)`. -/
theorem whittaker_eq_setIntegral (n : ℕ) {f : AdelicGL F (n + 1) → ℂ} (hfc : Continuous f)
    (hfinv : ∀ (a : RationalGL F (n + 1)) (g : AdelicGL F (n + 1)),
      f (AdelicGL.rational F _ a * g) = f g)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) :
    generalLinearWhittakerFunction F n ψ (fun _ => 1)
        (fun y => f (GeneralLinearGroupPoints.adelicEquiv F (n + 1) y)) 1 =
      unipotentNormalizer F (n + 1) • ∫ y in fd₀ F (n + 1),
        f (toMat F _ y) * starRingEnd ℂ (genericCharacter F n ψ (fun _ => 1) y)
          ∂Measure.haar := by
  have hcont : Continuous fun y : Points F (n + 1) =>
      f (GeneralLinearGroupPoints.adelicEquiv F (n + 1) y) :=
    hfc.comp (GeneralLinearGroupPoints.adelicHomeomorph F (n + 1)).continuous
  rw [generalLinearWhittakerFunction,
    RankinSelbergGlobal.Unfolding.subgroupCharacterCoefficient_eq_setIntegral
    F _ _ _ (RankinSelbergGlobal.Unfolding.continuous_genericCharacter F n ψ hψ.1 _).measurable
    (genericCharacter_mul_rational ψ hψ.2.2.1 n) _ hcont.measurable ?_ 1]
  · simp only [mul_one]
    rfl
  · intro k y
    obtain ⟨a, ha⟩ := toMat_mem_rational_of_mem_Γ₀ k.2
    rw [map_mul]
    have hk : GeneralLinearGroupPoints.adelicEquiv F (n + 1)
        ((k : unipotentAdelic F (n + 1)) : Points F (n + 1)) = AdelicGL.rational F _ a := ha
    rw [hk, hfinv]

/-- The generic coefficient as an integral over a fundamental domain of `N₀(F)`. -/
theorem coeff_eq_setIntegral (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) :
    coeff (r := r) (t := t) ψ φ s = unipotentNormalizer F (r + t + 2) •
      ∫ x in fd₀ F (r + t + 2), eisensteinSeries F φ s (toMat F _ x) *
        starRingEnd ℂ (genericChar ψ x) ∂Measure.haar := by
  have h := whittaker_eq_setIntegral (F := F) (r + t + 1) (f := eisensteinSeries F φ s)
    (continuous_eisensteinSeries hφ hσ hs) (eisensteinSeries_rational_mul hφ s) ψ hψ
  have hchar : ∀ x : unipotentAdelic F (r + t + 2),
      genericCharacter F (r + t + 1) ψ (fun _ => 1) x = genericChar ψ x := fun x =>
    (genericChar_eq ψ x).symm
  simp only [hchar] at h
  exact h

/-- **The unfolding of the generic coefficient.** -/
theorem coeff_eq_openCellIntegral (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {κ : ℝ≥0} (hκ : (haarN F r t).map (radicalCoord F r t) = κ • openCellHaar F r t) :
    coeff (r := r) (t := t) ψ φ s = ((κ : ℝ) : ℂ) * openCellIntegral ψ φ s := by
  have hcells := fun J => unfold_cell hφ hσ hs ψ hψ J
  have hsplit : ∫ x in fd₀ F (r + t + 2), eisensteinSeries F φ s (toMat F _ x) *
        starRingEnd ℂ (genericChar ψ x) ∂Measure.haar =
      ∫ x in cellDomain (openIndex r t), cellIntegrand φ s ψ (openIndex r t) x
        ∂Measure.haar := by
    have hfun : (fun x => eisensteinSeries F φ s (toMat F _ x) *
        starRingEnd ℂ (genericChar ψ x)) = fun x => ∑ J : PivotIndex (r + t + 2) (r + 1),
          (∑' q, cellTerm φ s J q (toMat F _ x)) * starRingEnd ℂ (genericChar ψ x) := by
      funext x
      rw [eisensteinSeries_eq_sum_cells hφ hσ hs, Finset.sum_mul]
    rw [hfun, integral_finsetSum _ (fun J _ => (hcells J).2.1),
      Finset.sum_eq_single (openIndex r t)]
    · exact (hcells _).2.2
    · intro J _ hJ
      rw [(hcells J).2.2]
      exact setIntegral_cellIntegrand_eq_zero hφ s ψ hψ J (fun h => hJ (Subtype.ext h))
        (hcells J).1
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hint : IntegrableOn (cellIntegrand φ s ψ (openIndex r t)) (cellDomain (openIndex r t))
      (haarH F r t) := by
    rw [IntegrableOn, haarH_eq, Measure.restrict_smul]
    exact (hcells _).1.smul_measure (ENNReal.inv_ne_top.mpr (haar_fd₀_ne_zero _))
  rw [coeff_eq_setIntegral hφ hσ hs ψ hψ, hsplit,
    ← setIntegral_cellDomain_openIndex hφ s ψ hψ hκ hint, haarH_eq, Measure.restrict_smul,
    integral_smul_measure, unipotentNormalizer_eq]

end Langlands.Global.CuspidalPairEisenstein.Unfolding

namespace Langlands.Global

/-- **Unfolding of the generic coefficient of a cuspidal-pair Eisenstein series**
(Shahidi 1978, Lemma 2.1; Shahidi 1981, proof of Theorem 5.1). -/
theorem cuspidalPairEisensteinUnfolding : CuspidalPairEisensteinUnfoldingStatement.{u} := by
  intro F _ _ _ r t T T' _ _ ψ hψ
  obtain ⟨κ, hκ0, hκ⟩ := CuspidalPairEisenstein.Unfolding.exists_map_radicalCoord_haarN F r t
  refine ⟨(κ : ℝ), by exact_mod_cast hκ0, fun φ hφ => ?_⟩
  obtain ⟨σ, hσ⟩ := CuspidalPairEisenstein.exists_normalBound hφ
  exact ⟨σ, fun s hs =>
    CuspidalPairEisenstein.Unfolding.coeff_eq_openCellIntegral hφ hσ hs ψ hψ hκ⟩

end Langlands.Global
