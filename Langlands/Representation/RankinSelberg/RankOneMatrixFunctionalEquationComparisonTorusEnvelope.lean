import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof
import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels

/-! # A finite smooth-coefficient envelope on the full diagonal torus -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Topology GeneralLinear Whittaker HarmonicAnalysis
open SquareIntegrableWhittakerTorusSum

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance torusEnvelopeTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance torusEnvelopeValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance torusEnvelopeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ n π) (v : V)

/-- A finite family of actual bi-smooth coefficients bounds the given
Whittaker coefficient on every diagonal times every integral matrix. -/
def TorusCoefficientEnvelope : Prop :=
  ∃ s : Finset (GodementJacquet.biSmoothMatrixCoefficients π),
    ∀ (a : Fin (n + 1) → F.Carrierˣ)
      (κ : Langlands.GeneralLinear (n + 1) F.Carrier),
      κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
      ‖ℓ.val (π (Iwasawa.diagonalUnits a * κ) v)‖ ≤
        ∑ f ∈ s, ‖f.val (Iwasawa.diagonalUnits a)‖

/-- Smoothness alone supplies the finite envelope. No irreducibility,
admissibility or analytic estimate is assumed. -/
theorem torusCoefficientEnvelope_of_smooth (hπ : IsSmooth π) :
    TorusCoefficientEnvelope F ψ π ℓ v := by
  classical
  let T := F.canonicalTopologicalData
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F.Carrier
  obtain ⟨R, -, hR⟩ :=
    Whittaker.smoothSimpleRootSupport F T n ψ V π hπ ℓ (modelMap π ℓ v)
  have hϖ1 : T.normalizedAbs (ϖ : F.Carrier) < 1 := by
    refine lt_of_le_of_ne ((T.normalizedAbs_le_one_iff_mem_integers _).mpr ?_) ?_
    · exact (Valuation.mem_integer_iff _ _).mpr hϖ.1.le
    · intro h
      exact hϖ.1.ne ((T.normalizedAbs_eq_one_iff_valuation_eq_one _).mp h)
  have hϖ0 : 0 < T.normalizedAbs (ϖ : F.Carrier) := T.normalizedAbs_pos ϖ.ne_zero
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt R ((one_lt_inv₀ hϖ0).mpr hϖ1)
  have hsupp : ∀ (e : Fin (n + 1) → ℤ)
      (κ : Langlands.GeneralLinear (n + 1) F.Carrier),
      κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
      ℓ.val (π (Iwasawa.torus ϖ e * κ) v) ≠ 0 →
      ∀ i : Fin n, -(b : ℤ) < e i.castSucc - e i.succ := by
    intro e κ hκ he i
    have h1 := hR (fun i => ϖ ^ e i) κ hκ he i
    beta_reduce at h1
    rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_zpow] at h1
    by_contra hle
    rw [not_lt] at hle
    have h2 : T.normalizedAbs (ϖ : F.Carrier) ^ (-(b : ℤ)) ≤
        T.normalizedAbs (ϖ : F.Carrier) ^ (e i.castSucc - e i.succ) :=
      zpow_le_zpow_right_of_le_one₀ hϖ0 hϖ1.le hle
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    exact absurd (hb.trans_le (h2.trans h1)) (lt_irrefl _)
  let shift : Fin (n + 1) → ℤ := fun i => (b : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ))
  have hstep : ∀ i : Fin n, shift i.castSucc - shift i.succ = b := by
    intro i
    simp only [shift, Fin.val_castSucc, Fin.val_succ]
    push_cast
    ring
  have hanti (e : Fin (n + 1) → ℤ)
      (κ : Langlands.GeneralLinear (n + 1) F.Carrier)
      (hκ : κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
      (he : ℓ.val (π (Iwasawa.torus ϖ e * κ) v) ≠ 0) : Antitone (e + shift) := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    have h1 := hsupp e κ hκ he i
    have h2 := hstep i
    simp only [Pi.add_apply]
    omega
  let K := Conductor.levelOpenSubgroup F.Carrier n 0
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    Conductor.isCompact_levelOpenSubgroup F.Carrier n 0
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S := Set.range (fun k : K => π k.val v)
  have hS : S.Finite :=
    ((Hecke.orbitMap_locallyConstant π (hπ v)).comp_continuous
      continuous_subtype_val).range_finite
  let : Fintype S := hS.fintype
  have hmem (κ : Langlands.GeneralLinear (n + 1) F.Carrier)
      (hκ : κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n) :
      π κ v ∈ S := by
    have hκK : κ ∈ K := by
      change κ ∈ Conductor.levelSubgroup F.Carrier n 0
      rwa [Conductor.levelSubgroup_zero]
    exact ⟨⟨κ, hκK⟩, rfl⟩
  have hL (j : S) :
      ∃ L : Module.Dual ℂ V, L ∈ smoothVectors π.dual ∧
        ∀ e : Fin (n + 1) → ℤ, Antitone (e + shift) →
          L (π (Iwasawa.torus ϖ e) j.val) =
            ℓ.val (π (Iwasawa.torus ϖ e) j.val) := by
    obtain ⟨r, -, -, L, hLs, -, hLeq⟩ :=
      exists_smooth_eq_on_antitone F T n ψ π hπ ℓ
        (π (Iwasawa.torus ϖ (-shift)) j.val) ϖ hϖ.1.le
    refine ⟨L, hLs, fun e he => ?_⟩
    have heq := hLeq (e + shift) he
    simpa only [← Module.End.mul_apply, ← map_mul, ← torus_add,
      add_neg_cancel_right] using heq
  choose L hLs hLeq using hL
  let coeff (j k : S) : GodementJacquet.biSmoothMatrixCoefficients π :=
    ⟨GodementJacquet.biSmoothCoefficient π ⟨L j, hLs j⟩ ⟨k.val, hπ k.val⟩,
      Submodule.subset_span ⟨_, _, rfl⟩⟩
  let s : Finset (GodementJacquet.biSmoothMatrixCoefficients π) :=
    Finset.univ.image (fun jk : S × S => coeff jk.1 jk.2)
  refine ⟨s, fun a κ hκ => ?_⟩
  by_cases hz : ℓ.val (π (Iwasawa.diagonalUnits a * κ) v) = 0
  · rw [hz, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  choose e he using fun i => hϖ.2 (a i : F.Carrier) (a i).ne_zero
  let ε : Fin (n + 1) → F.Carrierˣ := fun i => a i * (ϖ ^ e i)⁻¹
  have hε : ∀ i, ValuativeRel.valuation F.Carrier (ε i : F.Carrier) = 1 := by
    intro i
    change ValuativeRel.valuation F.Carrier (↑(a i * (ϖ ^ e i)⁻¹)) = 1
    rw [Units.val_mul, map_mul, he i, Units.val_inv_eq_inv_val,
      map_inv₀, Units.val_zpow_eq_zpow_val, map_zpow₀, mul_inv_cancel₀]
    exact zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  let δ := Iwasawa.diagonalUnits ε
  have hδ : δ ∈ Conductor.integralSubgroup
      (ValuativeRel.valuation F.Carrier).integer n :=
    Iwasawa.diagonalUnits_mem _ ε hε
  have ha : Iwasawa.diagonalUnits a = Iwasawa.torus ϖ e * δ := by
    rw [Iwasawa.torus, ← map_mul]
    congr 1
    funext i
    change a i = ϖ ^ e i * (a i * (ϖ ^ e i)⁻¹)
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  let j : S := ⟨π (δ * κ) v, hmem _ (mul_mem hδ hκ)⟩
  let k : S := ⟨π κ v, hmem _ hκ⟩
  have hraw : ℓ.val (π (Iwasawa.diagonalUnits a * κ) v) =
      ℓ.val (π (Iwasawa.torus ϖ e) j.val) := by
    rw [ha, mul_assoc, map_mul, Module.End.mul_apply]
  have hanti' : Antitone (e + shift) :=
    hanti e (δ * κ) (mul_mem hδ hκ) (by rwa [ha, mul_assoc] at hz)
  have heq := hLeq j e hanti'
  have hcoef : (coeff j k).val (Iwasawa.diagonalUnits a) =
      L j (π (Iwasawa.torus ϖ e) j.val) := by
    change L j (π (Iwasawa.diagonalUnits a) (π κ v)) = _
    rw [ha, ← Module.End.mul_apply, ← map_mul, mul_assoc,
      map_mul, Module.End.mul_apply]
  have hmember : coeff j k ∈ s :=
    Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩
  calc
    ‖ℓ.val (π (Iwasawa.diagonalUnits a * κ) v)‖ =
        ‖(coeff j k).val (Iwasawa.diagonalUnits a)‖ := by rw [hraw, hcoef, heq]
    _ ≤ ∑ f ∈ s, ‖f.val (Iwasawa.diagonalUnits a)‖ :=
      Finset.single_le_sum (s := s) (a := coeff j k)
        (f := fun f : GodementJacquet.biSmoothMatrixCoefficients π =>
          ‖f.val (Iwasawa.diagonalUnits a)‖)
        (fun _ _ => norm_nonneg _) hmember

end Langlands.RankinSelberg
