import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Unramified.MinusculeCosets
import Langlands.LocalField.Normalization.Proof

/-!
# Standard Hecke operators as finite sums over left cosets

On a vector fixed by `K = GL_(r+1)(O_F)`, the standard Hecke operator of the
double coset `K t_i K` acts as the finite sum `∑ ρ(x) v` over the labelled coset
representatives `x` of `MinusculeCosets`, whose labels are residue classes.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure GeneralLinear.Iwasawa MinusculeCosets

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance standardSumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance standardSumFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance standardSumFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance standardSumGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance standardSumGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance standardSumGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance standardSumGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance standardSumGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- The residue field is finite, used here as a fintype instance. -/
instance residueFieldFintype : Fintype F.canonicalTopologicalData.ResidueField :=
  @Fintype.ofFinite _ F.canonicalTopologicalData.finite_residueField

/-! ### The canonical uniformizer and residue lifts -/

/-- The canonical uniformizer is a uniformizing element of the canonical valuation. -/
theorem uniformizerUnit_isUniformizingElement :
    IsUniformizingElement (ValuativeRel.valuation F.Carrier)
      F.canonicalTopologicalData.uniformizerUnit := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hex : e (ValuativeRel.valuation F.Carrier
      (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)) = WithZero.exp (-1) := by
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value F.canonicalTopologicalData 1
    rw [zpow_one] at h
    exact h
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation F.Carrier y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation F.Carrier y)), ?_⟩
    have key : e (ValuativeRel.valuation F.Carrier y) = e (ValuativeRel.valuation F.Carrier
        (F.canonicalTopologicalData.uniformizerUnit : F.Carrier) ^
          (-WithZero.log (e (ValuativeRel.valuation F.Carrier y)))) := by
      rw [map_zpow₀, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
        WithZero.exp_log hy0]
    exact e.injective key

/-- A lift of each residue class to the field. -/
def residueLift (x : F.canonicalTopologicalData.ResidueField) : F.Carrier :=
  ((Function.surjInv (IsLocalRing.residue_surjective (R := F.canonicalTopologicalData.Integers))
    x : F.canonicalTopologicalData.Integers) : F.Carrier)

theorem residueLift_mem (x : F.canonicalTopologicalData.ResidueField) :
    residueLift F x ∈ (ValuativeRel.valuation F.Carrier).integer :=
  (Function.surjInv (IsLocalRing.residue_surjective (R := F.canonicalTopologicalData.Integers))
    x).property

theorem residue_eq_zero_iff (z : F.canonicalTopologicalData.Integers) :
    IsLocalRing.residue F.canonicalTopologicalData.Integers z = 0 ↔
      ValuativeRel.valuation F.Carrier (z : F.Carrier) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem residue_residueLift (x : F.canonicalTopologicalData.ResidueField) :
    IsLocalRing.residue F.canonicalTopologicalData.Integers
      (Function.surjInv (IsLocalRing.residue_surjective
        (R := F.canonicalTopologicalData.Integers)) x) = x :=
  Function.surjInv_eq _ x

/-- Distinct residue classes have lifts at distance one. -/
theorem residueLift_eq_of_lt_one {x y : F.canonicalTopologicalData.ResidueField}
    (h : ValuativeRel.valuation F.Carrier (residueLift F x - residueLift F y) < 1) : x = y := by
  have h0 := (residue_eq_zero_iff F
    (Function.surjInv (IsLocalRing.residue_surjective
        (R := F.canonicalTopologicalData.Integers)) x -
      Function.surjInv (IsLocalRing.residue_surjective
        (R := F.canonicalTopologicalData.Integers)) y)).2 h
  rw [map_sub, residue_residueLift, residue_residueLift, sub_eq_zero] at h0
  exact h0

/-- Every integral element is congruent to the lift of its residue class. -/
theorem exists_residueLift_lt_one {z : F.Carrier}
    (hz : z ∈ (ValuativeRel.valuation F.Carrier).integer) :
    ∃ x, ValuativeRel.valuation F.Carrier (z - residueLift F x) < 1 := by
  refine ⟨IsLocalRing.residue F.canonicalTopologicalData.Integers ⟨z, hz⟩, ?_⟩
  have h := (residue_eq_zero_iff F (⟨z, hz⟩ - Function.surjInv (IsLocalRing.residue_surjective
    (R := F.canonicalTopologicalData.Integers))
      (IsLocalRing.residue F.canonicalTopologicalData.Integers ⟨z, hz⟩))).1
    (by rw [map_sub, residue_residueLift, sub_self])
  exact h

/-! ### The standard diagonal as a subset torus -/

/-- The first `i` coordinates. -/
def initialSegment (r : ℕ) (i : Fin (r + 2)) : Finset (Fin (r + 1)) :=
  Finset.univ.filter fun j => j.val < i.val

theorem card_initialSegment (r : ℕ) (i : Fin (r + 2)) : (initialSegment r i).card = i.val := by
  rw [initialSegment, Fin.card_filter_val_lt]
  omega

theorem standardDiagonal_eq_subsetTorus (r : ℕ) (i : Fin (r + 2)) :
    standardDiagonal F r i =
      subsetTorus F.canonicalTopologicalData.uniformizerUnit (initialSegment r i) := by
  unfold standardDiagonal subsetTorus torus
  congr 1
  funext j
  by_cases hj : j.val < i.val <;> simp [subsetExponent, initialSegment, hj]

/-! ### The finite sum -/

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On a fixed vector, the standard Hecke operator is the sum of the translates by the
labelled coset representatives of its double coset. -/
theorem standardHecke_cornerAction_eq_sum {r : ℕ}
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsSmooth ρ)
    (i : Fin (r + 2)) (v : fixedVectors ρ (sphericalSubgroup F r)) :
    (Hecke.cornerAction (sphericalHaar F r) ρ hρ (sphericalOpenSubgroup F r)
        (sphericalOpenSubgroup_isCompact F r) (standardHeckeElement F r i) v : V) =
      ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
        ρ (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) α) v := by
  classical
  set ϖ := F.canonicalTopologicalData.uniformizerUnit
  have hϖ := uniformizerUnit_isUniformizingElement F
  let K := sphericalOpenSubgroup F r
  let x : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val →
      GeneralLinear (r + 1) F.Carrier := labelledRep ϖ (residueLift F)
  let s : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val →
      Set (GeneralLinear (r + 1) F.Carrier) :=
    fun α => (fun y => (x α)⁻¹ * y) ⁻¹' (K : Set (GeneralLinear (r + 1) F.Carrier))
  have hK : ∀ k, k ∈ (K : Set (GeneralLinear (r + 1) F.Carrier)) ↔
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r :=
    fun _ => Iff.rfl
  have hs : ∀ α, MeasurableSet (s α) := fun α =>
    (K.isOpen.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμ : ∀ α, sphericalHaar F r (s α) = 1 := by
    intro α
    rw [measure_preimage_mul]
    exact sphericalHaar_self F r
  have hfix : ∀ k ∈ (K : Set (GeneralLinear (r + 1) F.Carrier)), ρ k v = v :=
    fun k hk => v.property ⟨k, hk⟩
  change Hecke.heckeAction (sphericalHaar F r) ρ hρ
    (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra _ _ _ (standardHeckeElement F r i)) (v : V) = _
  rw [Hecke.heckeAction_apply]
  rw [Hecke.integratedAction_eq_sum_of_presentation _ ρ hρ _ (v : V) Finset.univ s
    (fun α => ρ (x α) v) (fun α _ => hs α) (fun α _ _ => by rw [hμ α]; exact ENNReal.one_lt_top)]
  · simp only [hμ, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    rfl
  intro y
  change standardHeckeElement F r i y • ρ y v = _
  rw [standardHeckeElement_apply]
  by_cases hy : y ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
      (standardDiagonal F r i)
  · rw [Set.indicator_of_mem hy, one_smul]
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Hecke.TestFunction.mem_doubleCosetSet _ _ _).1 hy
    rw [standardDiagonal_eq_subsetTorus] at hy ⊢
    obtain ⟨α, hα⟩ := exists_labelledRep (Λ := F.canonicalTopologicalData.ResidueField)
      (σ := residueLift F) hϖ (fun z hz => exists_residueLift_lt_one F hz)
      (card_initialSegment r i) hk₁ hk₂ rfl
    rw [Finset.sum_eq_single α]
    · rw [Set.indicator_of_mem (show _ ∈ s α from hα)]
      conv_lhs => rw [← mul_inv_cancel_left (x α) (k₁ * _ * k₂), map_mul,
        Module.End.mul_apply, hfix _ hα]
    · intro β _ hβ
      rw [Set.indicator_of_notMem]
      intro hβ'
      exact hβ (labelledRep_unique hϖ (fun a b h => residueLift_eq_of_lt_one F h) hβ' hα)
    · intro h
      exact absurd (Finset.mem_univ α) h
  · rw [Set.indicator_of_notMem hy, zero_smul]
    refine (Finset.sum_eq_zero fun α _ => Set.indicator_of_notMem (fun hα => hy ?_) _).symm
    obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := labelledRep_mem_doubleCoset (residueLift_mem F)
      (card_initialSegment r i) α (ϖ := ϖ) (n := r)
    rw [Hecke.TestFunction.mem_doubleCosetSet, standardDiagonal_eq_subsetTorus]
    refine ⟨k₁, hk₁, k₂ * ((x α)⁻¹ * y), mul_mem hk₂ hα, ?_⟩
    change y = k₁ * _ * (k₂ * ((labelledRep ϖ (residueLift F) α)⁻¹ * y))
    rw [← mul_assoc, ← hx, mul_inv_cancel_left]

end Langlands.Unramified
