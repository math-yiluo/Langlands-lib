import Langlands.Global.Arithmetic.CMSubfield
import Langlands.Global.Arithmetic.RationalGaloisModel
import Langlands.Global.Arithmetic.PadicSquareNonsquareProof

/-!
# A CM rational Galois model of a finite Galois p-adic field

For a finite Galois extension `Ω` of `ℚ_[p]`, the rational splitting field `M` of
`f · (X² - a) · (X² - d)` is a Galois CM field embedded in `Ω` with dense image. Here `f` is
the totally real defining polynomial of `Ω` from `RationalGaloisModel`, `a < 0` and `d > 0`
are rational squares in `ℚ_[p]`, and `d` is not a square in the splitting field of
`f · (X² - a)`. The square roots of `a` and `d` in `M` land in `ℚ_[p]` under the embedding.
An automorphism `flipPos` of `M` fixes the roots of `f · (X² - a)`, negates the square roots
of `d`, and commutes with every automorphism of `M`.
-/

noncomputable section

namespace Langlands.Global.CMRealization

open Polynomial IntermediateField NumberField FieldRealization

universe u

section SquareRoot

variable {L : Type*} [Field L] [CharZero L]

theorem aeval_X_sq_sub_C {c : ℚ} {r : L} :
    aeval r (X ^ 2 - C c) = 0 ↔ r ^ 2 = algebraMap ℚ L c := by
  simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]

theorem monic_X_sq_sub_C (c : ℚ) : (X ^ 2 - C c).Monic :=
  monic_X_pow_sub_C _ two_ne_zero

theorem map_X_sq_sub_C (c : ℚ) :
    (X ^ 2 - C c).map (algebraMap ℚ L) = X ^ 2 - C (algebraMap ℚ L c) := by
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]

/-- `X² - c` splits over a field containing a square root of `c`. -/
theorem splits_X_sq_sub_C {c : ℚ} {r : L} (hr : r ^ 2 = algebraMap ℚ L c) :
    ((X ^ 2 - C c).map (algebraMap ℚ L)).Splits := by
  rw [map_X_sq_sub_C]
  refine Splits.of_natDegree_eq_two (x := r) natDegree_X_pow_sub_C ?_
  simp only [eval_sub, eval_pow, eval_X, eval_C, hr, sub_self]

/-- A field over which `X² - c` splits contains a square root of `c`. -/
theorem exists_sq_of_splits {c : ℚ} (h : ((X ^ 2 - C c).map (algebraMap ℚ L)).Splits) :
    ∃ r : L, r ^ 2 = algebraMap ℚ L c := by
  rw [map_X_sq_sub_C] at h
  obtain ⟨r, hr⟩ := h.exists_eval_eq_zero (by rw [degree_X_pow_sub_C two_pos]; decide)
  refine ⟨r, ?_⟩
  simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hr

variable {K : Type*} [Field K] [CharZero K] [Algebra K L]

/-- A rational number that is a square in `K` has a square root in every extension of `K`. -/
theorem exists_sq_of_isSquare {c : ℚ} (hc : IsSquare (algebraMap ℚ K c)) :
    ∃ r : L, r ^ 2 = algebraMap ℚ L c := by
  obtain ⟨t, ht⟩ := hc
  refine ⟨algebraMap K L t, ?_⟩
  rw [pow_two, ← map_mul, ← ht]
  simp only [eq_ratCast, map_ratCast]

/-- A square root of a rational number that is a square in `K` lies in the image of `K`. -/
theorem exists_eq_algebraMap_of_sq {c : ℚ} {r : L} (hr : r ^ 2 = algebraMap ℚ L c)
    (hc : IsSquare (algebraMap ℚ K c)) : ∃ t : K, r = algebraMap K L t := by
  obtain ⟨t, ht⟩ := hc
  have h : r ^ 2 = (algebraMap K L t) ^ 2 := by
    rw [hr, pow_two (algebraMap K L t), ← map_mul, ← ht]
    simp only [eq_ratCast, map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨t, h⟩
  · exact ⟨-t, by rw [map_neg]; exact h⟩

end SquareRoot

section RealRoots

variable {K : Type*} [Field K] [CharZero K]

/-- A root of a nonzero rational polynomial that splits over `ℝ` is totally real. -/
theorem mem_maximalRealSubfield_of_root {f : ℚ[X]} (hf0 : f ≠ 0)
    (hf : (f.map (algebraMap ℚ ℝ)).Splits) {r : K} (hr : aeval r f = 0) :
    r ∈ maximalRealSubfield K := by
  intro φ
  have h₁ : aeval (φ r) f = 0 := by
    have h := aeval_algHom_apply φ.toRatAlgHom r f
    rw [hr, map_zero] at h
    exact h
  have hcomp : Complex.ofRealHom.comp (algebraMap ℚ ℝ) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hroot : ((f.map (algebraMap ℚ ℝ)).map Complex.ofRealHom).IsRoot (φ r) := by
    rw [Polynomial.map_map, hcomp, IsRoot, eval_map_algebraMap, h₁]
  obtain ⟨t, ht⟩ := hf.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) hroot
  rw [← ht]
  exact Complex.conj_ofReal t

/-- A square root of a positive rational number is totally real. -/
theorem mem_maximalRealSubfield_of_sq_pos {d : ℚ} (hd : 0 < d) {r : K}
    (hr : r ^ 2 = algebraMap ℚ K d) : r ∈ maximalRealSubfield K := by
  intro φ
  have hsq : (φ r) ^ 2 = algebraMap ℚ ℂ d := by
    rw [← map_pow, hr]
    exact φ.toRatAlgHom.commutes d
  exact Complex.conj_eq_iff_im.mpr (Langlands.Global.complexRoot_im_zero hd hsq)

end RealRoots

section Constants

variable (p : ℕ) [Fact p.Prime]

/-- A negative rational number that is a square in `ℚ_[p]`. -/
def negSq : ℚ :=
  Classical.choose (padicSquareNonsquare.{0} p inferInstance ℚ inferInstance inferInstance false)

theorem negSq_neg : negSq p < 0 := by
  obtain ⟨h, -, -⟩ := Classical.choose_spec
    (padicSquareNonsquare.{0} p inferInstance ℚ inferInstance inferInstance false)
  simp only [Bool.false_eq_true, ite_false] at h
  exact h

theorem negSq_isSquare : IsSquare (algebraMap ℚ ℚ_[p] (negSq p)) :=
  (Classical.choose_spec
    (padicSquareNonsquare.{0} p inferInstance ℚ inferInstance inferInstance false)).2.1

theorem negSq_not_isSquare : ¬ IsSquare (negSq p) := fun h =>
  (negSq_neg p).not_ge h.nonneg

/-- Splitting fields of rational polynomials are number fields. -/
instance splittingField_numberField (f : ℚ[X]) : NumberField f.SplittingField where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

variable (Ω : Type u) [Field Ω] [CharZero Ω] [Algebra ℚ_[p] Ω] [FiniteDimensional ℚ_[p] Ω]
  [IsGalois ℚ_[p] Ω]

/-- The totally real defining polynomial of `Ω` times `X² - a`. -/
def basePolynomial : ℚ[X] := rationalDefiningPolynomial p Ω * (X ^ 2 - C (negSq p))

/-- A positive rational number that is a square in `ℚ_[p]` and not a square in the splitting
field of `basePolynomial`. -/
def posSq : ℚ :=
  Classical.choose (padicSquareNonsquare.{0} p inferInstance
    (basePolynomial p Ω).SplittingField inferInstance inferInstance true)

theorem posSq_pos : 0 < posSq p Ω := by
  obtain ⟨h, -, -⟩ := Classical.choose_spec (padicSquareNonsquare.{0} p inferInstance
    (basePolynomial p Ω).SplittingField inferInstance inferInstance true)
  simp only [ite_true] at h
  exact h

theorem posSq_isSquare : IsSquare (algebraMap ℚ ℚ_[p] (posSq p Ω)) :=
  (Classical.choose_spec (padicSquareNonsquare.{0} p inferInstance
    (basePolynomial p Ω).SplittingField inferInstance inferInstance true)).2.1

theorem posSq_not_isSquare :
    ¬ IsSquare (algebraMap ℚ (basePolynomial p Ω).SplittingField (posSq p Ω)) :=
  (Classical.choose_spec (padicSquareNonsquare.{0} p inferInstance
    (basePolynomial p Ω).SplittingField inferInstance inferInstance true)).2.2

/-- The polynomial `f · (X² - a) · (X² - d)`. -/
def cmPolynomial : ℚ[X] := basePolynomial p Ω * (X ^ 2 - C (posSq p Ω))

theorem basePolynomial_monic : (basePolynomial p Ω).Monic := by
  obtain ⟨-, hm, -⟩ := rationalDefiningPolynomial_spec p Ω
  exact hm.mul (monic_X_sq_sub_C _)

theorem cmPolynomial_monic : (cmPolynomial p Ω).Monic :=
  (basePolynomial_monic p Ω).mul (monic_X_sq_sub_C _)

theorem basePolynomial_dvd : basePolynomial p Ω ∣ cmPolynomial p Ω := dvd_mul_right _ _

theorem negSq_dvd : X ^ 2 - C (negSq p) ∣ cmPolynomial p Ω :=
  dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem posSq_dvd : X ^ 2 - C (posSq p Ω) ∣ cmPolynomial p Ω := dvd_mul_left _ _

variable {p Ω} in
/-- A root of `cmPolynomial` is a root of `basePolynomial` or a square root of `d`. -/
theorem root_cases {K : Type*} [Field K] [CharZero K] {r : K} (hr : aeval r (cmPolynomial p Ω) = 0) :
    aeval r (basePolynomial p Ω) = 0 ∨ r ^ 2 = algebraMap ℚ K (posSq p Ω) := by
  rw [cmPolynomial, map_mul, mul_eq_zero, aeval_X_sq_sub_C] at hr
  exact hr

variable {p Ω} in
/-- A root of `basePolynomial` is a root of `f` or a square root of `a`. -/
theorem base_root_cases {K : Type*} [Field K] [CharZero K] {r : K}
    (hr : aeval r (basePolynomial p Ω) = 0) :
    aeval r (rationalDefiningPolynomial p Ω) = 0 ∨ r ^ 2 = algebraMap ℚ K (negSq p) := by
  rw [basePolynomial, map_mul, mul_eq_zero, aeval_X_sq_sub_C] at hr
  exact hr

end Constants

section Model

variable (p : ℕ) [Fact p.Prime] (Ω : Type u) [Field Ω] [CharZero Ω] [Algebra ℚ_[p] Ω]
  [FiniteDimensional ℚ_[p] Ω] [IsGalois ℚ_[p] Ω]

/-- The Type-0 CM rational Galois model of `Ω`. -/
abbrev cmModel : Type := (cmPolynomial p Ω).SplittingField

instance cmModel_isGalois : IsGalois ℚ (cmModel p Ω) := ⟨⟩

theorem cmPolynomial_splits : ((cmPolynomial p Ω).map (algebraMap ℚ Ω)).Splits := by
  obtain ⟨-, -, -, -, hf, -⟩ := rationalDefiningPolynomial_spec p Ω
  obtain ⟨a, ha⟩ := exists_sq_of_isSquare (L := Ω) (negSq_isSquare p)
  obtain ⟨d, hd⟩ := exists_sq_of_isSquare (L := Ω) (posSq_isSquare p Ω)
  rw [cmPolynomial, basePolynomial, Polynomial.map_mul, Polynomial.map_mul]
  exact (hf.mul (splits_X_sq_sub_C ha)).mul (splits_X_sq_sub_C hd)

/-- The CM model embeds into `Ω`. -/
def cmModelEmbedding : cmModel p Ω →ₐ[ℚ] Ω :=
  SplittingField.lift _ (cmPolynomial_splits p Ω)

theorem cmModelEmbedding_adjoin :
    IntermediateField.adjoin ℚ_[p] (Set.range (cmModelEmbedding p Ω)) = ⊤ := by
  obtain ⟨y, -, -, -, -, hy, hytop⟩ := rationalDefiningPolynomial_spec p Ω
  have hyroot : aeval y (cmPolynomial p Ω) = 0 := by
    rw [cmPolynomial, basePolynomial, map_mul, map_mul, hy, zero_mul, zero_mul]
  have hyrange : y ∈ (cmModelEmbedding p Ω).range := by
    rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range (cmModel p Ω)
      (cmPolynomial p Ω) (cmModelEmbedding p Ω)]
    exact Algebra.subset_adjoin ((cmPolynomial_monic p Ω).mem_rootSet.mpr hyroot)
  apply top_unique
  rw [← hytop]
  apply IntermediateField.adjoin_le_iff.mpr
  exact Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin _ _ hyrange)

theorem splits_of_dvd {g : ℚ[X]} (hg : g ∣ cmPolynomial p Ω) :
    (g.map (algebraMap ℚ (cmModel p Ω))).Splits :=
  (SplittingField.splits (cmPolynomial p Ω)).of_dvd
    ((cmPolynomial_monic p Ω).map _).ne_zero (Polynomial.map_dvd _ hg)

/-- A square root of `a` in the model. -/
def sqrtNeg : cmModel p Ω :=
  (exists_sq_of_splits (splits_of_dvd p Ω (negSq_dvd p Ω))).choose

theorem sqrtNeg_sq : sqrtNeg p Ω ^ 2 = algebraMap ℚ (cmModel p Ω) (negSq p) :=
  (exists_sq_of_splits (splits_of_dvd p Ω (negSq_dvd p Ω))).choose_spec

/-- A square root of `d` in the model. -/
def sqrtPos : cmModel p Ω :=
  (exists_sq_of_splits (splits_of_dvd p Ω (posSq_dvd p Ω))).choose

theorem sqrtPos_sq : sqrtPos p Ω ^ 2 = algebraMap ℚ (cmModel p Ω) (posSq p Ω) :=
  (exists_sq_of_splits (splits_of_dvd p Ω (posSq_dvd p Ω))).choose_spec

theorem sqrtNeg_ne_zero : sqrtNeg p Ω ≠ 0 := by
  intro h
  have := sqrtNeg_sq p Ω
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero] at this
  exact (negSq_neg p).ne this

theorem sqrtPos_ne_zero : sqrtPos p Ω ≠ 0 := by
  intro h
  have := sqrtPos_sq p Ω
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero] at this
  exact (posSq_pos p Ω).ne' this

theorem cmModelEmbedding_sqrtNeg :
    ∃ t : ℚ_[p], cmModelEmbedding p Ω (sqrtNeg p Ω) = algebraMap ℚ_[p] Ω t :=
  exists_eq_algebraMap_of_sq (by rw [← map_pow, sqrtNeg_sq, AlgHom.commutes])
    (negSq_isSquare p)

theorem cmModelEmbedding_sqrtPos :
    ∃ t : ℚ_[p], cmModelEmbedding p Ω (sqrtPos p Ω) = algebraMap ℚ_[p] Ω t :=
  exists_eq_algebraMap_of_sq (by rw [← map_pow, sqrtPos_sq, AlgHom.commutes])
    (posSq_isSquare p Ω)

theorem sqrtPos_mem_maximalRealSubfield : sqrtPos p Ω ∈ maximalRealSubfield (cmModel p Ω) :=
  mem_maximalRealSubfield_of_sq_pos (posSq_pos p Ω) (sqrtPos_sq p Ω)

/-- The model is generated over its totally real elements by the square root of `a`. -/
theorem maximalRealSubfield_adjoin_sqrtNeg :
    (maximalRealSubfield (cmModel p Ω))⟮sqrtNeg p Ω⟯ = ⊤ := by
  obtain ⟨-, hfm, -, hfr, -⟩ := rationalDefiningPolynomial_spec p Ω
  set R := maximalRealSubfield (cmModel p Ω)
  have hreal : ∀ r ∈ R, r ∈ R⟮sqrtNeg p Ω⟯ := fun r hr =>
    IntermediateField.algebraMap_mem _ (⟨r, hr⟩ : R)
  have hle : Algebra.adjoin ℚ ((cmPolynomial p Ω).rootSet (cmModel p Ω)) ≤
      ((R⟮sqrtNeg p Ω⟯).restrictScalars ℚ).toSubalgebra := by
    apply Algebra.adjoin_le
    intro r hr
    change r ∈ R⟮sqrtNeg p Ω⟯
    rcases root_cases ((cmPolynomial_monic p Ω).mem_rootSet.mp hr) with h | h
    · rcases base_root_cases h with h | h
      · exact hreal r (mem_maximalRealSubfield_of_root hfm.ne_zero hfr h)
      · rw [← sqrtNeg_sq] at h
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
        · rw [h]; exact mem_adjoin_simple_self _ _
        · rw [h]; exact neg_mem (mem_adjoin_simple_self _ _)
    · exact hreal r (mem_maximalRealSubfield_of_sq_pos (posSq_pos p Ω) h)
  rw [SplittingField.adjoin_rootSet] at hle
  exact eq_top_iff.mpr fun y _ => hle Algebra.mem_top

instance cmModel_isCMField : IsCMField (cmModel p Ω) :=
  isCMField_of_adjoin_eq_top (negSq_neg p) (sqrtNeg_sq p Ω)
    (maximalRealSubfield_adjoin_sqrtNeg p Ω)

theorem conjQ_sqrtNeg : conjQ (cmModel p Ω) (sqrtNeg p Ω) = -sqrtNeg p Ω :=
  conjQ_of_sq_neg (negSq_neg p) (sqrtNeg_sq p Ω)

theorem conjQ_sqrtPos : conjQ (cmModel p Ω) (sqrtPos p Ω) = sqrtPos p Ω :=
  (conjQ_eq_self_iff _).mpr (sqrtPos_mem_maximalRealSubfield p Ω)

end Model

section Flip

variable (p : ℕ) [Fact p.Prime] (Ω : Type u) [Field Ω] [CharZero Ω] [Algebra ℚ_[p] Ω]
  [FiniteDimensional ℚ_[p] Ω] [IsGalois ℚ_[p] Ω]

/-- The embedding of the splitting field of `basePolynomial` into the model. -/
def baseSplittingEmbedding : (basePolynomial p Ω).SplittingField →ₐ[ℚ] cmModel p Ω :=
  SplittingField.lift _ (splits_of_dvd p Ω (basePolynomial_dvd p Ω))

theorem mem_baseRange_of_root {r : cmModel p Ω} (hr : aeval r (basePolynomial p Ω) = 0) :
    r ∈ (baseSplittingEmbedding p Ω).fieldRange := by
  have h : r ∈ (baseSplittingEmbedding p Ω).range := by
    rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range
      (basePolynomial p Ω).SplittingField (basePolynomial p Ω) (baseSplittingEmbedding p Ω)]
    exact Algebra.subset_adjoin ((basePolynomial_monic p Ω).mem_rootSet.mpr hr)
  obtain ⟨z, hz⟩ := (AlgHom.mem_range _).mp h
  exact AlgHom.mem_fieldRange.mpr ⟨z, hz⟩

theorem posSq_not_isSquare_baseRange :
    ¬ IsSquare (algebraMap ℚ (baseSplittingEmbedding p Ω).fieldRange (posSq p Ω)) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp y.2
  apply posSq_not_isSquare p Ω
  refine ⟨z, (baseSplittingEmbedding p Ω).injective ?_⟩
  have hy' := congrArg (fun w : (baseSplittingEmbedding p Ω).fieldRange => (w : cmModel p Ω)) hy
  simp only [IntermediateField.coe_algebraMap_apply, IntermediateField.coe_mul] at hy'
  show baseSplittingEmbedding p Ω (algebraMap ℚ _ (posSq p Ω)) = baseSplittingEmbedding p Ω (z * z)
  rw [AlgHom.commutes, map_mul, hz, hy']

theorem exists_flipPos : ∃ s : cmModel p Ω ≃ₐ[ℚ] cmModel p Ω,
    (∀ r, aeval r (basePolynomial p Ω) = 0 → s r = r) ∧ s (sqrtPos p Ω) = -sqrtPos p Ω := by
  set K₁ := (baseSplittingEmbedding p Ω).fieldRange
  have hx : sqrtPos p Ω ^ 2 = algebraMap K₁ (cmModel p Ω) (algebraMap ℚ K₁ (posSq p Ω)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact sqrtPos_sq p Ω
  have hnx : (-sqrtPos p Ω) ^ 2 = algebraMap K₁ (cmModel p Ω) (algebraMap ℚ K₁ (posSq p Ω)) := by
    rw [neg_sq]
    exact hx
  have hmin : minpoly K₁ (-sqrtPos p Ω) = minpoly K₁ (sqrtPos p Ω) := by
    rw [Langlands.Global.squareRoot_minpoly (posSq_not_isSquare_baseRange p Ω) hx,
      Langlands.Global.squareRoot_minpoly (posSq_not_isSquare_baseRange p Ω) hnx]
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (cmModel p Ω)).mp hmin
  refine ⟨g.restrictScalars ℚ, fun r hr => g.commutes ⟨r, mem_baseRange_of_root p Ω hr⟩, ?_⟩
  exact hg

/-- An automorphism of the model fixing the roots of `basePolynomial` and negating the square
roots of `d`. -/
def flipPos : cmModel p Ω ≃ₐ[ℚ] cmModel p Ω := (exists_flipPos p Ω).choose

theorem flipPos_of_root {r : cmModel p Ω} (hr : aeval r (basePolynomial p Ω) = 0) :
    flipPos p Ω r = r :=
  (exists_flipPos p Ω).choose_spec.1 r hr

theorem flipPos_sqrtPos : flipPos p Ω (sqrtPos p Ω) = -sqrtPos p Ω :=
  (exists_flipPos p Ω).choose_spec.2

theorem flipPos_of_sq_pos {r : cmModel p Ω}
    (hr : r ^ 2 = algebraMap ℚ (cmModel p Ω) (posSq p Ω)) : flipPos p Ω r = -r := by
  rw [← sqrtPos_sq] at hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr with h | h
  · rw [h, flipPos_sqrtPos]
  · rw [h, map_neg, flipPos_sqrtPos]

theorem flipPos_sqrtNeg : flipPos p Ω (sqrtNeg p Ω) = sqrtNeg p Ω := by
  apply flipPos_of_root
  rw [basePolynomial, map_mul, aeval_X_sq_sub_C.mpr (sqrtNeg_sq p Ω), mul_zero]

/-- `flipPos` is central in the Galois group of the model. -/
theorem flipPos_central (σ : cmModel p Ω ≃ₐ[ℚ] cmModel p Ω) (x : cmModel p Ω) :
    σ (flipPos p Ω x) = flipPos p Ω (σ x) := by
  have h := AlgHom.ext_of_adjoin_eq_top (SplittingField.adjoin_rootSet (cmPolynomial p Ω))
    (φ₁ := (σ : cmModel p Ω →ₐ[ℚ] cmModel p Ω).comp (flipPos p Ω))
    (φ₂ := (flipPos p Ω : cmModel p Ω →ₐ[ℚ] cmModel p Ω).comp σ) (by
      intro r hr
      show σ (flipPos p Ω r) = flipPos p Ω (σ r)
      rcases root_cases ((cmPolynomial_monic p Ω).mem_rootSet.mp hr) with h | h
      · have hσ : aeval (σ r) (basePolynomial p Ω) = 0 := by
          rw [aeval_algHom_apply, h, map_zero]
        rw [flipPos_of_root p Ω h, flipPos_of_root p Ω hσ]
      · have hσ : (σ r) ^ 2 = algebraMap ℚ (cmModel p Ω) (posSq p Ω) := by
          rw [← map_pow, h, AlgEquiv.commutes]
        rw [flipPos_of_sq_pos p Ω h, flipPos_of_sq_pos p Ω hσ, map_neg])
  exact AlgHom.congr_fun h x

end Flip

end Langlands.Global.CMRealization
