import Langlands.Representation.Classification.ProductLeviChamberBoundProof
import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyStatement
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.CuspidalSupport.LeviGapVanishing
import Langlands.Group.GL.CartanProof
import Langlands.Group.GL.CartanCellCountProof
import Langlands.Analysis.CountableCellLpProof
import Langlands.Analysis.FiniteNatLatticeSummabilityProof
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-!
# Product-Levi tempered sufficiency from upper generalized Jacquet exponents

Proof of `GLProductLeviTemperedExponentSufficiencyStatement`.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace Langlands.ProductLeviTempered

open GeneralLinear Geometric ProductLeviChamber

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### The standard integral subgroup -/

theorem discreteValuation_integer : T.discreteValuation.integer = T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  ext x
  rw [Valuation.mem_integer_iff]
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change e (ValuativeRel.valuation F.Carrier x) ≤ 1 ↔ ValuativeRel.valuation F.Carrier x ≤ 1
  rw [← map_one e]
  exact e.strictMono.le_iff_le

theorem maximalCompact_eq (N : ℕ) :
    letI := T.valuativeRel
    CartanQuotient.maximalCompact T N =
      Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) N := by
  let := T.valuativeRel
  unfold CartanQuotient.maximalCompact Iwasawa.integralRange
  rw [discreteValuation_integer]

/-- The specified uniformizer is a uniformizing element for the discrete valuation. -/
theorem isUniformizingElement :
    Iwasawa.IsUniformizingElement T.discreteValuation
      (LocalFactor.PadicAbelian.uniformizerUnit T) := by
  have hu : T.discreteValuation ((LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrierˣ) :
      F.Carrier) = WithZero.exp (-1) := by
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value T 1
    rwa [zpow_one] at h
  constructor
  · rw [hu]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  · intro x hx
    have hvx : T.discreteValuation x ≠ 0 := (map_ne_zero _).mpr hx
    refine ⟨-WithZero.log (T.discreteValuation x), ?_⟩
    rw [hu, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
      WithZero.exp_log hvx]

/-! ### Cartan cells of the central quotient -/

section Cells

variable {n : ℕ} (C : BlockShape n)

/-- The product of the standard integral subgroups of the blocks. -/
def integralLevi :
    letI := T.topology
    OpenSubgroup (C.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact CuspidalSupport.LeviAdmissibility.integralLevi (K := F.Carrier) C

theorem mem_integralLevi (g : C.Levi F.Carrier) :
    letI := T.topology
    g ∈ integralLevi T C ↔ ∀ j, g j ∈ CartanQuotient.maximalCompact T (C.size j) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  simp only [maximalCompact_eq]
  exact CuspidalSupport.LeviAdmissibility.mem_integralLevi (K := F.Carrier) C

theorem isCompact_integralLevi :
    letI := T.topology
    IsCompact (integralLevi T C : Set (C.Levi F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact CuspidalSupport.LeviAdmissibility.isCompact_integralLevi (K := F.Carrier) C

/-- Every element of the product Levi lies, modulo the centre, in the double coset of
a blockwise normalized Cartan representative. -/
theorem exists_cell (g : C.Levi F.Carrier) :
    letI := T.topology
    ∃ lam : ∀ j, Fin (C.size j) → ℤ, (∀ j, CartanQuotient.Normalized (lam j)) ∧
      ∃ k₁ ∈ integralLevi T C, ∃ k₂ ∈ integralLevi T C,
        (QuotientGroup.mk g : C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) =
          QuotientGroup.mk (k₁ * leviRep T C lam * k₂) := by
  let := T.topology
  have hcart := fun j => Cartan.exists_cartan (isUniformizingElement T) (C.size j) (g j)
  choose lam hlam k₁ hk₁ k₂ hk₂ hg using hcart
  let last : ∀ j, Fin (C.size j) := fun j => ⟨C.size j - 1, by have := C.positive j; omega⟩
  let c : Fin C.length → ℤ := fun j => lam j (last j)
  let lam' : ∀ j, Fin (C.size j) → ℤ := fun j => CartanQuotient.shift (lam j) (-(c j))
  have hlast : ∀ j (i : Fin (C.size j)), i ≤ last j := by
    intro j i
    change i.val ≤ C.size j - 1
    have := i.isLt
    omega
  refine ⟨lam', fun j => ⟨?_, ?_, last j, ?_⟩, k₁, (mem_integralLevi T C _).mpr hk₁,
    k₂, (mem_integralLevi T C _).mpr hk₂, ?_⟩
  · intro x y hxy
    simp only [lam', CartanQuotient.shift]
    linarith [hlam j hxy]
  · intro i
    simp only [lam', CartanQuotient.shift, c]
    linarith [hlam j (hlast j i)]
  · simp [lam', CartanQuotient.shift, c]
  · let z : C.Levi F.Carrier :=
      C.blockScalarLevi F.Carrier (fun j => LocalFactor.PadicAbelian.uniformizerUnit T ^ c j)
    have hz : z ∈ Subgroup.center (C.Levi F.Carrier) := C.blockScalarLevi_mem_center F.Carrier _
    have hgz : g = z * (k₁ * leviRep T C lam' * k₂) := by
      funext j
      have hshift : lam j = CartanQuotient.shift (lam' j) (c j) := by
        funext i
        simp [lam', CartanQuotient.shift]
      have hrep : Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) (lam j) =
          GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T ^ c j) *
            CartanQuotient.representative T (lam' j) := by
        change CartanQuotient.representative T (lam j) = _
        rw [hshift]
        exact CartanQuotient.representative_shift T (lam' j) (c j)
      change g j = GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T ^ c j) *
        (k₁ j * CartanQuotient.representative T (lam' j) * k₂ j)
      rw [hg j, hrep]
      have hcomm := Subgroup.mem_center_iff.mp
        (GeneralLinear.scalarToCenter (n := C.size j)
          (LocalFactor.PadicAbelian.uniformizerUnit T ^ c j)).2 (k₁ j)
      change k₁ j * GeneralLinear.scalar _ = GeneralLinear.scalar _ * k₁ j at hcomm
      rw [← mul_assoc (k₁ j), hcomm, mul_assoc, mul_assoc, mul_assoc]
    rw [hgz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, one_mul]

end Cells

/-! ### Measures of cells -/

section Measure

variable {n : ℕ} (C : BlockShape n)

/-- The actual Cartan cell of a family of exponent tuples in the central quotient. -/
def cellQ (lam : ∀ j, Fin (C.size j) → ℤ) :
    Set (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
  letI := T.topology
  {q | ∃ k₁ ∈ integralLevi T C, ∃ k₂ ∈ integralLevi T C,
    q = QuotientGroup.mk (k₁ * leviRep T C lam * k₂)}

/-- The Cartan cell of an antidominant family is covered by boundedly many left
translates of the image of the integral subgroup, up to the inverse radial weight. -/
theorem measure_cellQ_le (hcount : CartanQuotient.CartanCellCountStatement.{uF}) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∃ cc : Fin C.length → ℝ, (∀ j, 0 ≤ cc j) ∧
      ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
        [μ.IsHaarMeasure] (lam : ∀ j, Fin (C.size j) → ℤ), (∀ j, Antitone (lam j)) →
        μ (cellQ T C lam) ≤
          ENNReal.ofReal (∏ j, cc j * (CartanQuotient.delta T (lam j))⁻¹) *
            μ (QuotientGroup.mk '' (integralLevi T C : Set (C.Levi F.Carrier))) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  classical
  have hc := fun j => hcount p F T (C.size j)
  choose cc hcc using hc
  have hcc0 : ∀ j, 0 ≤ cc j := by
    intro j
    obtain ⟨R, hR, -⟩ := hcc j 0 antitone_const
    have hd : 0 < (CartanQuotient.delta T (0 : Fin (C.size j) → ℤ))⁻¹ :=
      inv_pos.mpr (CartanQuotient.delta_pos T _)
    by_contra h
    push Not at h
    have : cc j * (CartanQuotient.delta T (0 : Fin (C.size j) → ℤ))⁻¹ < 0 :=
      mul_neg_of_neg_of_pos h hd
    linarith [(Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card)]
  refine ⟨cc, hcc0, fun μ _ lam hlam => ?_⟩
  choose R hRcard hRcover using fun j => hcc j (lam j) (hlam j)
  let Rprod : Finset (C.Levi F.Carrier) := Fintype.piFinset R
  let S0 : Set (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    QuotientGroup.mk '' (integralLevi T C : Set (C.Levi F.Carrier))
  have hcover : cellQ T C lam ⊆ ⋃ r ∈ Rprod,
      (fun q => (QuotientGroup.mk (r * leviRep T C lam) :
        C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) * q) '' S0 := by
    rintro q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hk₁' := (mem_integralLevi T C k₁).mp hk₁
    have hk₂' := (mem_integralLevi T C k₂).mp hk₂
    choose r hr k hk heq using fun j => hRcover j (k₁ j) (hk₁' j) (k₂ j) (hk₂' j)
    refine Set.mem_biUnion (x := (fun j => r j : C.Levi F.Carrier))
      (Fintype.mem_piFinset.mpr hr) ⟨QuotientGroup.mk (fun j => k j : C.Levi F.Carrier),
        ⟨_, (mem_integralLevi T C _).mpr hk, rfl⟩, ?_⟩
    change QuotientGroup.mk _ * QuotientGroup.mk _ = QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul]
    congr 1
    funext j
    exact (heq j).symm
  have htrans : ∀ r : C.Levi F.Carrier,
      μ ((fun q => (QuotientGroup.mk (r * leviRep T C lam) :
        C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) * q) '' S0) = μ S0 := by
    intro r
    rw [Set.image_mul_left, MeasureTheory.measure_preimage_mul]
  calc μ (cellQ T C lam)
      ≤ μ (⋃ r ∈ Rprod, (fun q => (QuotientGroup.mk (r * leviRep T C lam) :
          C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) * q) '' S0) :=
        MeasureTheory.measure_mono hcover
    _ ≤ ∑ r ∈ Rprod, μ ((fun q => (QuotientGroup.mk (r * leviRep T C lam) :
          C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) * q) '' S0) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ = (Rprod.card : ℝ≥0∞) * μ S0 := by
        simp only [htrans, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (∏ j, cc j * (CartanQuotient.delta T (lam j))⁻¹) * μ S0 := by
        gcongr
        rw [Fintype.card_piFinset, Nat.cast_prod]
        have h : (∏ i, ((R i).card : ℝ≥0∞)) = ENNReal.ofReal (∏ i, ((R i).card : ℝ)) := by
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Nat.cast_nonneg _)]
          simp only [ENNReal.ofReal_natCast]
        rw [h]
        apply ENNReal.ofReal_le_ofReal
        exact Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => hRcard j

theorem measure_image_integralLevi_lt_top :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure],
      μ (QuotientGroup.mk '' (integralLevi T C : Set (C.Levi F.Carrier))) < ⊤ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _
  exact ((isCompact_integralLevi T C).image QuotientGroup.continuous_mk).measure_lt_top

end Measure

/-! ### Coefficients on cells -/

section Coefficient

variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The chamber bound holds uniformly on the whole Cartan double cosets, because the
integral translates of a smooth vector and of a smooth functional form finite sets. -/
theorem cell_coefficient_bound :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V), IsAdmissible ρ →
      UpperExponentHypothesis T C ρ →
      ∀ (ℓ : SmoothDual ρ) (v : V) (η : ℝ), 0 < η →
        ∃ cb : ℝ, ∀ lam : ∀ j, Fin (C.size j) → ℤ, (∀ j, CartanQuotient.Normalized (lam j)) →
          ∀ k₁ ∈ integralLevi T C, ∀ k₂ ∈ integralLevi T C,
            ‖matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (k₁ * leviRep T C lam * k₂)‖ ≤
              cb * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hexp ℓ v η hη
  classical
  have hchamber := fun (ℓ' : SmoothDual ρ) (w : V) => chamber_bound T C ρ hadm hexp ℓ' w η hη
  choose cfun hcfun using hchamber
  let K := integralLevi T C
  have hK := isCompact_integralLevi T C
  have hfinv : (Compact.orbit (ρ.comp K.toSubgroup.subtype) v).Finite :=
    Set.finite_coe_iff.mp (Compact.finite_orbit_of_smooth ρ hadm.1 K hK v)
  have hfinℓ : (Compact.orbit ((smoothContragredient ρ).comp K.toSubgroup.subtype) ℓ).Finite :=
    Set.finite_coe_iff.mp (Compact.finite_orbit_of_smooth (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) K hK ℓ)
  let Sv := hfinv.toFinset
  let Sℓ := hfinℓ.toFinset
  refine ⟨∑ ℓ' ∈ Sℓ, ∑ w ∈ Sv, |cfun ℓ' w|, fun lam hlam k₁ hk₁ k₂ hk₂ => ?_⟩
  let ℓ' : SmoothDual ρ := smoothContragredient ρ k₁⁻¹ ℓ
  let w : V := ρ k₂ v
  have hℓ' : ℓ' ∈ Sℓ := (Set.Finite.mem_toFinset _).mpr ⟨⟨k₁⁻¹, K.inv_mem hk₁⟩, rfl⟩
  have hw : w ∈ Sv := (Set.Finite.mem_toFinset _).mpr ⟨⟨k₂, hk₂⟩, rfl⟩
  have heq : matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (k₁ * leviRep T C lam * k₂) =
      matrixCoefficient ρ (ℓ' : Module.Dual ℂ V) w (leviRep T C lam) := by
    change (ℓ : Module.Dual ℂ V) (ρ (k₁ * leviRep T C lam * k₂) v) =
      (ρ.dual k₁⁻¹ (ℓ : Module.Dual ℂ V)) (ρ (leviRep T C lam) (ρ k₂ v))
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Representation.dual_apply,
      Module.Dual.transpose_apply, inv_inv]
    rfl
  rw [heq]
  have hprod_nonneg : 0 ≤ ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) :=
    Finset.prod_nonneg fun j _ => Real.rpow_nonneg (CartanQuotient.delta_pos T _).le _
  have habs : |cfun ℓ' w| ≤ ∑ ℓ'' ∈ Sℓ, ∑ w' ∈ Sv, |cfun ℓ'' w'| :=
    calc |cfun ℓ' w| ≤ ∑ w' ∈ Sv, |cfun ℓ' w'| :=
          Finset.single_le_sum (f := fun w' => |cfun ℓ' w'|) (fun _ _ => abs_nonneg _) hw
      _ ≤ ∑ ℓ'' ∈ Sℓ, ∑ w' ∈ Sv, |cfun ℓ'' w'| :=
          Finset.single_le_sum (f := fun ℓ'' => ∑ w' ∈ Sv, |cfun ℓ'' w'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hℓ'
  calc ‖matrixCoefficient ρ (ℓ' : Module.Dual ℂ V) w (leviRep T C lam)‖
      ≤ cfun ℓ' w * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) := hcfun ℓ' w lam hlam
    _ ≤ |cfun ℓ' w| * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hprod_nonneg
    _ ≤ (∑ ℓ'' ∈ Sℓ, ∑ w' ∈ Sv, |cfun ℓ'' w'|) *
          ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) :=
        mul_le_mul_of_nonneg_right habs hprod_nonneg

end Coefficient

/-! ### The lattice of cells -/

section Lattice

variable {n : ℕ} (C : BlockShape n)

/-- The exponent family of a point of the fundamental-coweight lattice. -/
def latticeTuple (m : FundIndex C → ℕ) : ∀ j, Fin (C.size j) → ℤ :=
  ∑ s, m s • fundTuple C s

theorem latticeTuple_apply (m : FundIndex C → ℕ) (j : Fin C.length) (x : Fin (C.size j)) :
    latticeTuple C m j x = ∑ s, (m s : ℤ) * fundTuple C s j x := by
  simp [latticeTuple, Finset.sum_apply, nsmul_eq_mul]

theorem fundTuple_nonneg (s : FundIndex C) (j : Fin C.length) (x : Fin (C.size j)) :
    0 ≤ fundTuple C s j x := by
  unfold fundTuple
  split_ifs
  · unfold fund
    split_ifs <;> norm_num
  · simp

theorem fundTuple_last (s : FundIndex C) (j : Fin C.length) :
    fundTuple C s j ⟨C.size j - 1, by have := C.positive j; omega⟩ = 0 := by
  obtain ⟨j0, t⟩ := s
  unfold fundTuple
  by_cases h : j = j0
  · subst h
    have := fundIndex_lt C ⟨j, t⟩
    simp only [↓reduceIte]
    unfold fund
    rw [ite_eq_right]
    intro h'
    change C.size j - 1 < t.val + 1 at h'
    omega
  · simp [h]

theorem latticeTuple_normalized (m : FundIndex C → ℕ) (j : Fin C.length) :
    CartanQuotient.Normalized (latticeTuple C m j) := by
  refine ⟨antitone_sum_fundTuple C Finset.univ m j, fun i => ?_,
    ⟨C.size j - 1, by have := C.positive j; omega⟩, ?_⟩
  · rw [latticeTuple_apply]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (fundTuple_nonneg C s j i)
  · rw [latticeTuple_apply]
    exact Finset.sum_eq_zero fun s _ => by rw [fundTuple_last, mul_zero]

theorem latticeTuple_fundCoeff (lam : ∀ j, Fin (C.size j) → ℤ)
    (hlam : ∀ j, CartanQuotient.Normalized (lam j)) :
    latticeTuple C (fundCoeff C lam) = lam :=
  (normalized_eq_sum_fundTuple C lam hlam).symm

theorem prod_delta_latticeTuple (m : FundIndex C → ℕ) :
    ∏ j, CartanQuotient.delta T (latticeTuple C m j) = ∏ s, fundWeight T C s ^ m s := by
  have hj : ∀ j, CartanQuotient.delta T (latticeTuple C m j) =
      ∏ s, CartanQuotient.delta T (fundTuple C s j) ^ m s := by
    intro j
    unfold latticeTuple
    rw [Finset.sum_apply, delta_sum]
    apply Finset.prod_congr rfl
    intro s _
    rw [Pi.smul_apply, delta_nsmul]
  simp only [hj]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  rw [Finset.prod_pow]
  rfl

end Lattice

/-- The product-Levi tempered sufficiency, given the Cartan coset count. -/
theorem tempered_of_cellCount (hcount : CartanQuotient.CartanCellCountStatement.{uF}) :
    GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ C S ω hirr hadm hω hunit hcore _ _ _ μ _
  let := T.leviTopologicalGroup C
  classical
  have hSne : Nontrivial S.V := by
    let := hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (C.Levi F.Carrier)) S.ρ.asModule
  let c := T.unitaryCentralCharacterOfBlockScalar C S.ρ ω hadm.1 hω hunit
  refine ⟨hadm, c, fun ℓ v ε hε => ?_⟩
  let η : ℝ := ε / (4 * (2 + ε))
  have hη : 0 < η := by positivity
  obtain ⟨cb, hcb⟩ := cell_coefficient_bound T C S.ρ hadm hcore ℓ v η hη
  obtain ⟨cc, hcc0, hcc⟩ := measure_cellQ_le T C hcount
  let P : ℝ := 2 + ε
  have hP : 0 < P := by positivity
  let w : FundIndex C → ℝ := fun s => fundWeight T C s
  have hw0 : ∀ s, 0 < w s := fun s => fundWeight_pos T C s
  have hw1 : ∀ s, w s < 1 := fun s => fundWeight_lt_one T C s
  let y : FundIndex C → ℝ := fun s => w s ^ ((1 : ℝ) / 2 - η)
  have hy0 : ∀ s, 0 ≤ y s := fun s => Real.rpow_nonneg (hw0 s).le _
  let x : FundIndex C → ℝ := fun s => y s ^ P * (w s)⁻¹
  have hx0 : ∀ s, 0 ≤ x s := fun s =>
    mul_nonneg (Real.rpow_nonneg (hy0 s) _) (inv_nonneg.mpr (hw0 s).le)
  have hx1 : ∀ s, x s < 1 := by
    intro s
    have hκ : 0 < ((1 : ℝ) / 2 - η) * P + -1 := by
      have : ((1 : ℝ) / 2 - η) * P + -1 = ε / 4 := by
        simp only [η, P]
        field_simp
        ring
      rw [this]
      positivity
    have hxs : x s = w s ^ (((1 : ℝ) / 2 - η) * P + -1) := by
      simp only [x, y]
      rw [Real.rpow_add (hw0 s), Real.rpow_mul (hw0 s).le, Real.rpow_neg_one]
    rw [hxs]
    exact Real.rpow_lt_one (hw0 s).le (hw1 s) hκ
  let b : (FundIndex C → ℕ) → ℝ≥0∞ := fun m => ENNReal.ofReal (|cb| * ∏ s, y s ^ m s)
  let S0 : Set (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    QuotientGroup.mk '' (integralLevi T C : Set (C.Levi F.Carrier))
  have hS0 : μ S0 < ⊤ := measure_image_integralLevi_lt_top T C μ
  have hp0 : ENNReal.ofReal P ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hP
  have hmeas := c.aestronglyMeasurable_coefficientNorm (ℓ : Module.Dual ℂ S.V) v (hadm.1 v) μ
  have hcover : (⋃ m, cellQ T C (latticeTuple C m)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨lam, hlam, k₁, hk₁, k₂, hk₂, hq⟩ := exists_cell T C g
    refine Set.mem_iUnion.mpr ⟨fundCoeff C lam, k₁, hk₁, k₂, hk₂, ?_⟩
    rw [latticeTuple_fundCoeff C lam hlam]
    exact hq
  have hbound : ∀ m q, q ∈ cellQ T C (latticeTuple C m) →
      ‖c.coefficientNorm (ℓ : Module.Dual ℂ S.V) v q‖ₑ ≤ b m := by
    rintro m q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    rw [Real.enorm_of_nonneg (c.coefficientNorm_nonneg _ _ _),
      UnitaryCentralCharacter.coefficientNorm_mk]
    apply ENNReal.ofReal_le_ofReal
    have h := hcb (latticeTuple C m) (latticeTuple_normalized C m) k₁ hk₁ k₂ hk₂
    have hprod : ∏ j, CartanQuotient.delta T (latticeTuple C m j) ^ ((1 : ℝ) / 2 - η) =
        ∏ s, y s ^ m s := by
      rw [Real.finsetProd_rpow _ _ (fun j _ => (CartanQuotient.delta_pos T _).le),
        prod_delta_latticeTuple, ← Real.finsetProd_rpow _ _
          (fun s _ => pow_nonneg (fundWeight_pos T C s).le _)]
      apply Finset.prod_congr rfl
      intro s _
      exact (Real.rpow_pow_comm (fundWeight_pos T C s).le _ _).symm
    rw [hprod] at h
    calc _ ≤ cb * ∏ s, y s ^ m s := h
      _ ≤ |cb| * ∏ s, y s ^ m s :=
        mul_le_mul_of_nonneg_right (le_abs_self _)
          (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _)
  have halg : ∀ m : FundIndex C → ℕ,
      (|cb| * ∏ s, y s ^ m s) ^ P *
          ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹ =
        (|cb| ^ P * ∏ j, cc j) * ∏ s, x s ^ m s := by
    intro m
    rw [Real.mul_rpow (abs_nonneg _) (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _),
      ← Real.finsetProd_rpow _ _ (fun s _ => pow_nonneg (hy0 s) _), Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, prod_delta_latticeTuple, ← Finset.prod_inv_distrib]
    have h1 : ∏ s, (y s ^ m s) ^ P = ∏ s, (y s ^ P) ^ m s :=
      Finset.prod_congr rfl fun s _ => (Real.rpow_pow_comm (hy0 s) _ _).symm
    have h2 : ∏ s, x s ^ m s = (∏ s, (y s ^ P) ^ m s) * ∏ s, (fundWeight T C s ^ m s)⁻¹ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _
      simp only [x, w]
      rw [mul_pow, inv_pow]
    rw [h1, h2]
    ring
  have hterm : ∀ m : FundIndex C → ℕ,
      b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m)) ≤
        (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) * ENNReal.ofReal (∏ s, x s ^ m s) := by
    intro m
    rw [ENNReal.toReal_ofReal hP.le]
    have hμ := hcc μ (latticeTuple C m) (fun j => (latticeTuple_normalized C m j).1)
    have hnn1 : 0 ≤ |cb| * ∏ s, y s ^ m s :=
      mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _)
    have hnn2 : 0 ≤ ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹ :=
      Finset.prod_nonneg fun j _ =>
        mul_nonneg (hcc0 j) (inv_nonneg.mpr (CartanQuotient.delta_pos T _).le)
    calc b m ^ P * μ (cellQ T C (latticeTuple C m))
        ≤ b m ^ P * (ENNReal.ofReal
            (∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹) * μ S0) := by
          gcongr
      _ = ENNReal.ofReal ((|cb| * ∏ s, y s ^ m s) ^ P *
            ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹) * μ S0 := by
          simp only [b]
          rw [ENNReal.ofReal_rpow_of_nonneg hnn1 hP.le, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hnn1 _)]
      _ = (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ENNReal.ofReal (∏ s, x s ^ m s) := by
          rw [halg, ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (Finset.prod_nonneg fun j _ => hcc0 j))]
          ring
  have hlattice : (∑' m : FundIndex C → ℕ, ENNReal.ofReal (∏ s, x s ^ m s)) < ⊤ := by
    have h := finiteNatLatticeENNRealSummability (FundIndex C) x hx0 hx1 0 le_rfl
    simpa only [Real.rpow_eq_pow, Real.rpow_zero, one_mul] using h
  have hsum : (∑' m, b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m))) < ⊤ := by
    calc (∑' m, b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m)))
        ≤ ∑' m : FundIndex C → ℕ, (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ENNReal.ofReal (∏ s, x s ^ m s) := ENNReal.tsum_le_tsum hterm
      _ = (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ∑' m : FundIndex C → ℕ, ENNReal.ofReal (∏ s, x s ^ m s) := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS0) hlattice
  exact countableCellLpUpper _ (FundIndex C → ℕ) μ _ (ENNReal.ofReal P) hp0 ENNReal.ofReal_ne_top
    hmeas (fun m => cellQ T C (latticeTuple C m)) hcover b hbound hsum

end Langlands.ProductLeviTempered

namespace Langlands

universe uF uV

/-- Product-Levi tempered sufficiency from upper generalized Jacquet exponents. -/
theorem glProductLeviTemperedExponentSufficiency :
    GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV} :=
  ProductLeviTempered.tempered_of_cellCount GeneralLinear.CartanQuotient.cartanCellCount

end Langlands
