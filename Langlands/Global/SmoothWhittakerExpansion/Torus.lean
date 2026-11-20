import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerBasic
import Langlands.Global.RankinSelberg.UnipotentConjugationModulus
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # Reduction of the Whittaker expansion to the standard generic character

For nonzero `m_0, …, m_{r-1} ∈ F` let `t = diag(e_0, …, e_{r-1}, 1)` with
`e_k = ∏_{k ≤ j < r} m_j`, so that `e_i / e_{i+1} = m_i`. Conjugation `n ↦ t n t⁻¹` is a continuous
automorphism of `N_{r+1}(𝔸)` preserving `N_{r+1}(F)`; it preserves Haar measure and the normalized
quotient measure on `N(F) \ N(𝔸)`, and it carries the standard generic character to the one with
coefficients `m`. Hence `W_{ψ,m}(g) = W_{ψ,1}(t g)` for every function left invariant under
`GL_{r+1}(F)`, and left multiplication by the upper-left block `t'` of `t` permutes
`N_r(F) \ GL_r(F)`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.SmoothWhittakerExpansion

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  Langlands.Global.RankinSelbergGlobal.Unfolding
  Langlands.Global.RankinSelbergGlobal.UnipotentConjugationModulus

local instance torusSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance torusSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

section Weights

/-- The weight `e_k = ∏_{k ≤ j < r} m_j` at position `k` of `Fin (r + 1)`. -/
def torusWeight (m : Fin r → F) (k : Fin (r + 1)) : F :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ j.castSucc), m j

omit [NumberField F] in
theorem torusWeight_ne_zero {m : Fin r → F} (hm : ∀ i, m i ≠ 0) (k : Fin (r + 1)) :
    torusWeight m k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => hm j

omit [NumberField F] in
theorem torusWeight_last (m : Fin r → F) : torusWeight m (Fin.last r) = 1 := by
  rw [torusWeight]
  convert Finset.prod_empty
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_le]
  exact Fin.castSucc_lt_last j

omit [NumberField F] in
theorem torusWeight_castSucc (m : Fin r → F) (i : Fin r) :
    torusWeight m i.castSucc = m i * torusWeight m i.succ := by
  rw [torusWeight, torusWeight]
  have e : Finset.univ.filter (fun j : Fin r => i.castSucc ≤ j.castSucc) =
      insert i (Finset.univ.filter (fun j : Fin r => i.succ ≤ j.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.castSucc_le_castSucc_iff, Fin.succ_le_castSucc_iff]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact h.symm.le
      · exact h.le
  rw [e, Finset.prod_insert]
  simp

/-- The units `e_k ∈ 𝔸ˣ`. -/
def torusUnit {m : Fin r → F} (hm : ∀ i, m i ≠ 0) (k : Fin (r + 1)) : (Adeles F)ˣ :=
  Units.map (algebraMap F (Adeles F)).toMonoidHom (Units.mk0 _ (torusWeight_ne_zero hm k))

theorem coe_torusUnit {m : Fin r → F} (hm : ∀ i, m i ≠ 0) (k : Fin (r + 1)) :
    (torusUnit hm k : Adeles F) = algebraMap F (Adeles F) (torusWeight m k) := rfl

/-- The upper-left block `t' = diag(e_0, …, e_{r-1})` of `t`, in `GL_r(F)`. -/
def torusLevi {m : Fin r → F} (hm : ∀ i, m i ≠ 0) : RationalGL F r where
  val := Matrix.diagonal fun i => torusWeight m i.castSucc
  inv := Matrix.diagonal fun i => (torusWeight m i.castSucc)⁻¹
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ (torusWeight_ne_zero hm _)]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [inv_mul_cancel₀ (torusWeight_ne_zero hm _)]

/-- The rational point `t = diag(t', 1)`. -/
abbrev torusPoint {m : Fin r → F} (hm : ∀ i, m i ≠ 0) : Points F (r + 1) :=
  cornerAdelicPoint F r (torusLevi hm)

theorem matrixOf_torusPoint {m : Fin r → F} (hm : ∀ i, m i ≠ 0) :
    matrixOf (torusPoint hm) = Matrix.diagonal fun k => (torusUnit hm k : Adeles F) := by
  ext a b
  rw [matrixOf, torusPoint, cornerAdelicPoint, MulEquiv.apply_symm_apply, AdelicGL.rational_apply,
    cornerEmbedding_apply, Matrix.diagonal_apply, coe_torusUnit]
  by_cases ha : (a : ℕ) < r
  · by_cases hb : (b : ℕ) < r
    · simp only [ha, hb, ↓reduceDIte]
      simp only [torusLevi, Matrix.diagonal_apply, Fin.ext_iff]
      split_ifs with h
      · congr 2
      · simp
    · simp only [ha, hb, ↓reduceDIte, map_zero]
      rw [eq_comm, ite_eq_right_iff]
      intro h
      exact absurd (h ▸ ha) hb
  · simp only [ha, ↓reduceDIte]
    have hal : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
    split_ifs with h
    · subst h
      rw [hal, torusWeight_last, map_one]
    · rw [map_zero]

end Weights

section Conjugation

variable {m : Fin r → F} (hm : ∀ i, m i ≠ 0)

theorem torusPoint_eq_rational :
    torusPoint hm = AdelicGroupPoints.rational F (Scheme F (r + 1))
      ((GeneralLinearGroupPoints.rationalEquiv F (r + 1)).symm
        (cornerEmbedding r (torusLevi hm))) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [torusPoint, cornerAdelicPoint, MulEquiv.apply_symm_apply,
    GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]

theorem torusPoint_mem_rationalSubgroup :
    torusPoint hm ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)) :=
  ⟨_, (torusPoint_eq_rational hm).symm⟩

/-- Conjugation `n ↦ t n t⁻¹` on `N_{r+1}(𝔸)`. -/
def torusConj : unipotentAdelic F (r + 1) ≃ₜ* unipotentAdelic F (r + 1) :=
  QuotientIntegration.subgroupAutomorphism (unipotentAdelic F (r + 1))
    (conjugation (torusPoint hm)) (conj_mem_iff_of_diagonal (matrixOf_torusPoint hm))

theorem coe_torusConj (n : unipotentAdelic F (r + 1)) :
    ((torusConj hm n : unipotentAdelic F (r + 1)) : Points F (r + 1)) =
      torusPoint hm * n * (torusPoint hm)⁻¹ := rfl

theorem coe_torusConj_symm (n : unipotentAdelic F (r + 1)) :
    (((torusConj hm).symm n : unipotentAdelic F (r + 1)) : Points F (r + 1)) =
      (torusPoint hm)⁻¹ * n * torusPoint hm := by
  rw [torusConj, QuotientIntegration.subgroupAutomorphism_symm_apply]
  rfl

/-- A point of `N_n(𝔸)` that is rational lies in `N_n(F)`. -/
theorem mem_rationalSubgroup_of_rational {n : ℕ} (x : unipotentAdelic F n)
    (hx : (x : Points F n) ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) := by
  obtain ⟨l, hl⟩ := (mem_unipotentRationalImage_iff F n x).mp
    ((mem_unipotentRationalImage_iff_mem_inf F n x).mpr ⟨hx, x.property⟩)
  have h : (l : unipotentAdelic F n) = x := Subtype.ext hl
  rw [← h]
  exact l.property

theorem torusConj_mem (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))) :
    torusConj hm l ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
      (upperUnipotent F (r + 1)) := by
  apply mem_rationalSubgroup_of_rational
  rw [coe_torusConj]
  have ht := torusPoint_mem_rationalSubgroup hm
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht (mem_rationalSubgroup_of_unipotent F l))
    (Subgroup.inv_mem _ ht)

theorem torusConj_symm_mem (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))) :
    (torusConj hm).symm l ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
      (upperUnipotent F (r + 1)) := by
  apply mem_rationalSubgroup_of_rational
  rw [coe_torusConj_symm]
  have ht := torusPoint_mem_rationalSubgroup hm
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht)
    (mem_rationalSubgroup_of_unipotent F l)) ht

theorem torusConj_mem_iff (x : unipotentAdelic F (r + 1)) :
    torusConj hm x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
      (upperUnipotent F (r + 1)) ↔
    x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)) := by
  constructor
  · intro h
    have := torusConj_symm_mem hm ⟨_, h⟩
    simpa using this
  · intro h
    exact torusConj_mem hm ⟨x, h⟩

/-- Conjugation by `t` carries the standard generic character to the one with coefficients
`m`. -/
theorem genericCharacter_torusConj (ψ : AddChar (Adeles F) ℂ) (n : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ (fun _ => 1) (torusConj hm n) = genericCharacter F r ψ m n := by
  simp only [genericCharacter, map_one, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change matrixOf (torusPoint hm * (n : Points F (r + 1)) * (torusPoint hm)⁻¹) i.castSucc i.succ =
    algebraMap F (Adeles F) (m i) * matrixOf (n : Points F (r + 1)) i.castSucc i.succ
  rw [matrixOf_conj_apply (matrixOf_torusPoint hm), coe_torusUnit, torusWeight_castSucc,
    map_mul, ← coe_torusUnit hm i.succ]
  have h1 : (torusUnit hm i.succ : Adeles F) * (((torusUnit hm i.succ)⁻¹ : (Adeles F)ˣ) :
      Adeles F) = 1 := Units.mul_inv _
  calc algebraMap F (Adeles F) (m i) * (torusUnit hm i.succ : Adeles F) *
        matrixOf (n : Points F (r + 1)) i.castSucc i.succ *
        (((torusUnit hm i.succ)⁻¹ : (Adeles F)ˣ) : Adeles F)
      = algebraMap F (Adeles F) (m i) * matrixOf (n : Points F (r + 1)) i.castSucc i.succ *
        ((torusUnit hm i.succ : Adeles F) * (((torusUnit hm i.succ)⁻¹ : (Adeles F)ˣ) :
          Adeles F)) := by ring
    _ = _ := by rw [h1, mul_one]

end Conjugation

section Measure

variable {n : ℕ}

local instance torusUnipotentLocallyCompact :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

local instance torusQuotientBorelSpace :
    BorelSpace (AdelicSubgroupPoints.RationalQuotient F (Scheme F n) (upperUnipotent F n)) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F (Scheme F n) (upperUnipotent F n)

variable (φ : unipotentAdelic F n ≃ₜ* unipotentAdelic F n)
  (hφ : ∀ x, φ x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) ↔
    x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n))

include hφ in
theorem symm_mem_iff (x : unipotentAdelic F n) :
    φ.symm x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) ↔
      x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) := by
  rw [← hφ (φ.symm x), ContinuousMulEquiv.apply_symm_apply]

include hφ in
/-- The preimage of the fundamental domain of `N_n(F)` under `φ` is again a strict
fundamental domain. -/
theorem existsUnique_mem_preimage_fundamentalDomain (x : unipotentAdelic F n) :
    ∃! l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n),
      (l : unipotentAdelic F n) * x ∈ φ ⁻¹' unipotentFundamentalDomain F n := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  obtain ⟨l, hl, hlu⟩ := LeftCosetSpace.fundamentalDomain_unique _ hΛd (φ x)
  refine ⟨⟨φ.symm l, (symm_mem_iff φ hφ _).mpr l.property⟩, ?_, ?_⟩
  · show φ (φ.symm (l : unipotentAdelic F n) * x) ∈ unipotentFundamentalDomain F n
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
    exact hl
  · intro l' hl'
    have h1 : ((⟨φ l', (hφ _).mpr l'.property⟩ :
        AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)) :
          unipotentAdelic F n) * φ x ∈ unipotentFundamentalDomain F n := by
      have : φ ((l' : unipotentAdelic F n) * x) ∈ unipotentFundamentalDomain F n := hl'
      rwa [map_mul] at this
    have h2 := hlu _ h1
    apply Subtype.ext
    have h3 := congrArg (fun k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n)
      (upperUnipotent F n) => φ.symm (k : unipotentAdelic F n)) h2
    simpa using h3

include hφ in
theorem isFundamentalDomain_preimage :
    IsFundamentalDomain (AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n))
      (φ ⁻¹' unipotentFundamentalDomain F n) (Measure.haar : Measure (unipotentAdelic F n)) := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛd
  exact IsFundamentalDomain.mk'
    (φ.continuous.measurable (LeftCosetSpace.measurableSet_fundamentalDomain _ hΛd)
      ).nullMeasurableSet (existsUnique_mem_preimage_fundamentalDomain φ hφ)

include hφ in
/-- A continuous automorphism of `N_n(𝔸)` preserving `N_n(F)` preserves Haar measure: the image
of Haar is a multiple of Haar, and the automorphism permutes the strict fundamental domains of
`N_n(F)`, of equal finite positive mass. -/
theorem measurePreserving_haar_of_rational :
    MeasurePreserving φ (Measure.haar : Measure (unipotentAdelic F n)) Measure.haar := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛd
  have := compactSpace_unipotentRationalQuotient F n
  have hαm : Measurable φ := φ.continuous.measurable
  refine ⟨hαm, ?_⟩
  have hκ := Measure.isMulLeftInvariant_eq_smul
    (Measure.map φ (Measure.haar : Measure (unipotentAdelic F n)))
    (Measure.haar : Measure (unipotentAdelic F n))
  set c := Measure.haarScalarFactor
    (Measure.map φ (Measure.haar : Measure (unipotentAdelic F n)))
    (Measure.haar : Measure (unipotentAdelic F n))
  have hsNm := LeftCosetSpace.measurableSet_fundamentalDomain _ hΛd
  have hfd1 := isFundamentalDomain_preimage φ hφ
  have hfd2 := LeftCosetSpace.isFundamentalDomain _ hΛd
    (Measure.haar : Measure (unipotentAdelic F n))
  have heq := hfd1.measure_eq hfd2
  have h1 : Measure.map φ (Measure.haar : Measure (unipotentAdelic F n))
      (unipotentFundamentalDomain F n) =
      (Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n) :=
    (Measure.map_apply hαm hsNm).trans heq
  have hne0 : (Measure.haar : Measure (unipotentAdelic F n))
      (unipotentFundamentalDomain F n) ≠ 0 := by
    rw [haar_unipotentFundamentalDomain]
    exact ENNReal.inv_ne_zero.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_top _ _ _)
  have hnetop : (Measure.haar : Measure (unipotentAdelic F n))
      (unipotentFundamentalDomain F n) ≠ ∞ := by
    rw [haar_unipotentFundamentalDomain]
    exact ENNReal.inv_ne_top.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero _ _ _)
  have hc : (c : ℝ≥0∞) = 1 := by
    rw [hκ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    exact (ENNReal.mul_left_inj hne0 hnetop).mp (by rw [one_mul]; exact h1)
  have hc' : c = 1 := by exact_mod_cast hc
  rw [hκ, hc', one_smul]

/-- The measurable equivalence of `N_n(F) \ N_n(𝔸)` induced by `φ`. -/
def quotientMap :
    AdelicSubgroupPoints.RationalQuotient F (Scheme F n) (upperUnipotent F n) ≃ᵐ
      AdelicSubgroupPoints.RationalQuotient F (Scheme F n) (upperUnipotent F n) :=
  (QuotientIntegration.quotientAutomorphism _ φ hφ).toMeasurableEquiv

theorem quotientMap_mk (x : unipotentAdelic F n) :
    quotientMap φ hφ (LeftCosetSpace.mk _ x) = LeftCosetSpace.mk _ (φ x) := rfl

include hφ in
/-- The induced map of `N_n(F) \ N_n(𝔸)` preserves the normalized quotient measure. -/
theorem measurePreserving_quotientMap :
    MeasurePreserving (quotientMap φ hφ)
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F n)
        (upperUnipotent F n))
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F n)
        (upperUnipotent F n)) := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛd
  have hmp := measurePreserving_haar_of_rational φ hφ
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  have hbase : Measure.map (quotientMap φ hφ)
      (LeftCosetSpace.quotientMeasure _ (Measure.haar : Measure (unipotentAdelic F n))
        (unipotentFundamentalDomain F n)) =
      LeftCosetSpace.quotientMeasure _ (Measure.haar : Measure (unipotentAdelic F n))
        (unipotentFundamentalDomain F n) := by
    rw [LeftCosetSpace.quotientMeasure,
      Measure.map_map (quotientMap φ hφ).measurable (LeftCosetSpace.measurable_mk _)]
    have hcomp : (quotientMap φ hφ) ∘ LeftCosetSpace.mk _ = LeftCosetSpace.mk _ ∘ φ := rfl
    rw [hcomp, ← Measure.map_map (LeftCosetSpace.measurable_mk _) hemb.measurable]
    have hres : Measure.map φ ((Measure.haar : Measure (unipotentAdelic F n)).restrict
        (unipotentFundamentalDomain F n)) =
        (Measure.haar : Measure (unipotentAdelic F n)).restrict
          (φ.symm ⁻¹' unipotentFundamentalDomain F n) := by
      have h1 := hemb.restrict_map (Measure.haar : Measure (unipotentAdelic F n))
        (φ.symm ⁻¹' unipotentFundamentalDomain F n)
      have h2 : φ ⁻¹' (φ.symm ⁻¹' unipotentFundamentalDomain F n) =
          unipotentFundamentalDomain F n := by
        ext x
        simp
      rw [h2, hmp.map_eq] at h1
      exact h1.symm
    rw [hres]
    exact LeftCosetSpace.quotientMeasure_eq _ _
      (isFundamentalDomain_preimage φ.symm (symm_mem_iff φ hφ))
      (LeftCosetSpace.isFundamentalDomain _ hΛd _)
  refine ⟨(quotientMap φ hφ).measurable, ?_⟩
  rw [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure, Measure.map_smul,
    AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, hbase]
  exact (quotientMap φ hφ).measurable.aemeasurable

end Measure

section Whittaker

variable {m : Fin r → F} (hm : ∀ i, m i ≠ 0)

/-- **`W_{ψ,m}(g) = W_{ψ,1}(t g)`** for every function left invariant under `GL_{r+1}(F)`.
Substitute `n ↦ t n t⁻¹` on `N(F) \ N(𝔸)`; it preserves the normalized quotient measure and
carries the standard character to the character with coefficients `m`. -/
theorem generalLinearWhittakerFunction_eq_torus (ψ : AddChar (Adeles F) ℂ)
    (hψ1 : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (f : Points F (r + 1) → ℂ)
    (hf : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
    (g : Points F (r + 1)) :
    generalLinearWhittakerFunction F r ψ m f g =
      generalLinearWhittakerFunction F r ψ (fun _ => 1) f (torusPoint hm * g) := by
  have hmp := measurePreserving_quotientMap (torusConj hm) (torusConj_mem_iff hm)
  rw [generalLinearWhittakerFunction, generalLinearWhittakerFunction,
    subgroupCharacterCoefficient_eq_integral, subgroupCharacterCoefficient_eq_integral,
    ← hmp.integral_comp' (coefficientIntegrand F _ _ (genericCharacter F r ψ fun _ => 1) f
      (torusPoint hm * g))]
  congr 1
  funext q
  obtain ⟨l0, hl0⟩ := exists_out_mk_eq
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
    (torusConj hm (Quotient.out q))
  have hq : quotientMap (torusConj hm) (torusConj_mem_iff hm) q =
      LeftCosetSpace.mk _ (torusConj hm (Quotient.out q)) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp only [coefficientIntegrand]
  rw [hq, hl0, genericCharacter_mul, genericCharacter_rational F r ψ hψ1 _ l0, one_mul,
    genericCharacter_torusConj]
  congr 1
  rw [Subgroup.coe_mul, coe_torusConj]
  have e : ((l0 : unipotentAdelic F (r + 1)) : Points F (r + 1)) *
      (torusPoint hm * ((Quotient.out q : unipotentAdelic F (r + 1)) : Points F (r + 1)) *
        (torusPoint hm)⁻¹) * (torusPoint hm * g) =
      ((l0 : unipotentAdelic F (r + 1)) : Points F (r + 1)) *
        (torusPoint hm * (((Quotient.out q : unipotentAdelic F (r + 1)) : Points F (r + 1)) *
          g)) := by
    group
  rw [e, hf _ (mem_rationalSubgroup_of_unipotent F l0),
    hf _ (torusPoint_mem_rationalSubgroup hm)]

omit [NumberField F] in
/-- Conjugation by an invertible diagonal matrix preserves the upper unitriangular matrices. -/
theorem conj_mem_upperUnipotent_of_diagonal {g : RationalGL F r} {d d' : Fin r → F}
    (hg : (g : Matrix (Fin r) (Fin r) F) = Matrix.diagonal d)
    (hg' : ((g⁻¹ : RationalGL F r) : Matrix (Fin r) (Fin r) F) = Matrix.diagonal d')
    (hdd : ∀ i, d i * d' i = 1) {x : RationalGL F r}
    (hx : x ∈ GeneralLinear.upperUnipotent r F) :
    g * x * g⁻¹ ∈ GeneralLinear.upperUnipotent r F := by
  have he : ∀ i j, ((g * x * g⁻¹ : RationalGL F r) : Matrix (Fin r) (Fin r) F) i j =
      d i * (x : Matrix (Fin r) (Fin r) F) i j * d' j := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hg, hg', Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [he, hx.1 hij, mul_zero, zero_mul]
  · change ((g * x * g⁻¹ : RationalGL F r) : Matrix (Fin r) (Fin r) F) i i = 1
    rw [he, hx.2 i, mul_one, hdd]

omit [NumberField F] in
theorem torusLevi_conj_mem {x : RationalGL F r} (hx : x ∈ GeneralLinear.upperUnipotent r F) :
    torusLevi hm * x * (torusLevi hm)⁻¹ ∈ GeneralLinear.upperUnipotent r F :=
  conj_mem_upperUnipotent_of_diagonal rfl rfl
    (fun _ => mul_inv_cancel₀ (torusWeight_ne_zero hm _)) hx

omit [NumberField F] in
theorem torusLevi_inv_conj_mem {x : RationalGL F r}
    (hx : x ∈ GeneralLinear.upperUnipotent r F) :
    (torusLevi hm)⁻¹ * x * (torusLevi hm)⁻¹⁻¹ ∈ GeneralLinear.upperUnipotent r F :=
  conj_mem_upperUnipotent_of_diagonal rfl (by rw [inv_inv]; rfl)
    (fun _ => inv_mul_cancel₀ (torusWeight_ne_zero hm _)) hx

/-- Left multiplication by `t'` permutes `N_r(F) \ GL_r(F)`. -/
def cosetEquiv : UnipotentRationalCosets F r ≃ UnipotentRationalCosets F r :=
  Quotient.congr (Equiv.mulLeft (torusLevi hm)) fun a b => by
    simp only [QuotientGroup.rightRel_apply, Equiv.coe_mulLeft]
    have e : torusLevi hm * b * (torusLevi hm * a)⁻¹ =
        torusLevi hm * (b * a⁻¹) * (torusLevi hm)⁻¹ := by group
    rw [e, mem_rationalUpperUnipotent_iff, mem_rationalUpperUnipotent_iff]
    refine ⟨torusLevi_conj_mem hm, fun h => ?_⟩
    have h2 := torusLevi_inv_conj_mem hm h
    have e2 : (torusLevi hm)⁻¹ * (torusLevi hm * (b * a⁻¹) * (torusLevi hm)⁻¹) *
        (torusLevi hm)⁻¹⁻¹ = b * a⁻¹ := by group
    rwa [e2] at h2

theorem cosetEquiv_apply (q : UnipotentRationalCosets F r) :
    cosetEquiv hm q = Quotient.mk _ (torusLevi hm * Quotient.out q) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

theorem cornerAdelicPoint_mul (a b : RationalGL F r) :
    cornerAdelicPoint F r (a * b) = cornerAdelicPoint F r a * cornerAdelicPoint F r b := by
  simp only [cornerAdelicPoint, map_mul]

variable (F r) in
/-- **Reduction to the standard generic character.** For nonzero `m`, there is a permutation
`σ` of `N_r(F) \ GL_r(F)` (left multiplication by `t' = diag(e_0, …, e_{r-1})`) such that for
every function `f` on `GL_{r+1}(𝔸)` left invariant under `GL_{r+1}(F)`, every coset `q` and
every `g`, `W_{ψ,m}(diag(q, 1) g) = W_{ψ,1}(diag(σ q, 1) g)`. -/
theorem exists_cosetEquiv_genericCharacter (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (m : Fin r → F) (hm : ∀ i, m i ≠ 0) :
    ∃ σ : UnipotentRationalCosets F r ≃ UnipotentRationalCosets F r,
      ∀ (f : Points F (r + 1) → ℂ),
        (∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x) →
        ∀ (q : UnipotentRationalCosets F r) (g : Points F (r + 1)),
          generalLinearWhittakerFunction F r ψ m f (cornerAdelicPoint F r q.out * g) =
            generalLinearWhittakerFunction F r ψ (fun _ => 1) f
              (cornerAdelicPoint F r (σ q).out * g) := by
  refine ⟨cosetEquiv hm, fun f hf q g => ?_⟩
  rw [generalLinearWhittakerFunction_eq_torus hm ψ hψ.2.2.1 f hf, ← mul_assoc, torusPoint,
    ← cornerAdelicPoint_mul, ← padRational_eq_cornerAdelicPoint,
    ← padRational_eq_cornerAdelicPoint]
  have hrel : QuotientGroup.rightRel (rationalUpperUnipotent F r) (cosetEquiv hm q).out
      (torusLevi hm * q.out) :=
    Quotient.exact ((Quotient.out_eq _).trans (cosetEquiv_apply hm q))
  exact whittaker_padRational_of_rightRel F ψ hψ f hf (Nat.le_succ r) hrel g

end Whittaker

end Langlands.Global.SmoothWhittakerExpansion
