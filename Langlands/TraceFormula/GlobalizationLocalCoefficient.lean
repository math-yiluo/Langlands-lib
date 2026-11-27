import Langlands.Global.CompletionPadic
import Langlands.Representation.GodementJacquet.SupercuspidalCutoffTests
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.BaseChange.CuspForm

/-! # Compact local coefficients for supercuspidal globalization -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u w

open MeasureTheory
open Langlands.Global Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula

variable {K : Type u} [Field K] [NumberField K] (v : FinitePlace K) {n : ℕ}
variable {V : Type w} [AddCommGroup V] [Module ℂ V]

set_option hygiene false in
local notation "Aᵥ" => GeneralLinear n (v.adicCompletion K)
set_option hygiene false in
local notation "D" => CompletionPadic.topologicalData v
set_option hygiene false in
local notation "N" => (D).determinantNorm n

/-- The determinant norm on the p-adic realization detects the original completion's
valuation-one determinants. -/
theorem completion_determinantNorm_eq_one_iff (g : Aᵥ) :
    N g = 1 ↔ Valued.v (GeneralLinear.determinant g : v.adicCompletion K) = 1 := by
  let x : v.adicCompletion K := GeneralLinear.determinant g
  have hnorm : N g = 1 ↔ (D).normalizedAbs x = 1 := by
    rw [← (D).determinantNorm_coe n g]
    exact ⟨fun h => by rw [h]; rfl, fun h => Units.ext (NNReal.eq h)⟩
  rw [hnorm, (D).normalizedAbs_eq_one_iff_valuation_eq_one]
  let := (D).valuativeRel
  let W := ValuativeRel.valuation (v.adicCompletion K)
  have hle : W x ≤ 1 ↔ Valued.v x ≤ 1 := by
    rw [← map_one W, ← W.vle_iff_le, CompletionPadic.topologicalData_vle, map_one]
  have hge : 1 ≤ W x ↔ 1 ≤ Valued.v x := by
    rw [← map_one W, ← W.vle_iff_le, CompletionPadic.topologicalData_vle, map_one]
  exact le_antisymm_iff.trans ((and_congr hle hge).trans le_antisymm_iff.symm)

section Separation

variable [LocallyCompactSpace Aᵥ] [TotallyDisconnectedSpace Aᵥ]

/-- A smooth dual vector detecting a vector can be normalized to have pairing one. -/
theorem exists_normalized_smoothCoefficient
    (ρ : Representation ℂ Aᵥ V) (hirr : ρ.IsIrreducible) (hρ : GeneralLinear.IsSupercuspidal ρ) :
    ∃ (z : V) (ℓ : Module.Dual ℂ V), IsSmoothVector ρ.dual ℓ ∧ ℓ z = 1 := by
  let : IsTopologicalGroup Aᵥ := (D).generalLinearTopologicalGroup n
  let : T2Space Aᵥ := (D).generalLinearT2Space n
  let : ρ.IsIrreducible := hirr
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ Aᵥ) ρ.asModule
  obtain ⟨z, hz⟩ := exists_ne (0 : V)
  obtain ⟨ℓ, hℓ, _, hℓz⟩ := CompactCoefficientSemisimplicity.exists_smooth_dual_separating
    ρ hρ.1.1 ⊥ (a := z) (by
      change z ∉ (⊥ : Submodule ℂ V)
      simpa only [Submodule.mem_bot] using hz)
  exact ⟨(ℓ z)⁻¹ • z, ℓ, hℓ, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hℓz]⟩

end Separation

/-- The coefficient `g ↦ ℓ(ρ(g⁻¹)z)` on determinant-unit matrices, extended by zero. -/
def globalizationLocalCoefficient (hn : 0 < n) (ρ : Representation ℂ Aᵥ V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) : V →ₗ[ℂ] SchwartzBruhat Aᵥ := by
  let : IsTopologicalGroup Aᵥ := (D).generalLinearTopologicalGroup n
  let : T2Space Aᵥ := (D).generalLinearT2Space n
  exact (Hecke.TestFunction.pullback (Homeomorph.inv Aᵥ)).toLinearMap.comp
    ((SchwartzBruhat.extendZero ((D).isOpen_ker_determinantNorm n)).comp
      (GodementJacquet.supercuspidalDeterminantUnitCoefficient D hn ρ hρ ℓ hℓ))

/-- The cutoff agrees with the inverse matrix coefficient on determinant-unit matrices. -/
theorem globalizationLocalCoefficient_apply (hn : 0 < n) (ρ : Representation ℂ Aᵥ V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (z : V) (g : Aᵥ) (hg : N g = 1) :
    globalizationLocalCoefficient v hn ρ hρ ℓ hℓ z g = ℓ (ρ g⁻¹ z) := by
  have hi : g⁻¹ ∈ (N).ker := by simp [hg]
  unfold globalizationLocalCoefficient
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Hecke.TestFunction.pullback_apply,
    LinearMap.comp_apply]
  exact SchwartzBruhat.extendZero_apply_of_mem _ _ hi

/-- The cutoff vanishes off the determinant-unit subgroup. -/
theorem globalizationLocalCoefficient_apply_of_ne_one (hn : 0 < n) (ρ : Representation ℂ Aᵥ V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (z : V) (g : Aᵥ) (hg : N g ≠ 1) :
    globalizationLocalCoefficient v hn ρ hρ ℓ hℓ z g = 0 := by
  have hi : g⁻¹ ∉ (N).ker := by simp [hg]
  unfold globalizationLocalCoefficient
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Hecke.TestFunction.pullback_apply,
    LinearMap.comp_apply]
  exact SchwartzBruhat.extendZero_apply_of_not_mem _ _ hi

/-- Left translation by a determinant-unit matrix is the action on the input vector. -/
theorem globalizationLocalCoefficient_translate (hn : 0 < n) (ρ : Representation ℂ Aᵥ V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (z : V) (k g : Aᵥ) (hk : N k = 1) :
    globalizationLocalCoefficient v hn ρ hρ ℓ hℓ (ρ k z) g =
      globalizationLocalCoefficient v hn ρ hρ ℓ hℓ z (k⁻¹ * g) := by
  have hnorm : N (k⁻¹ * g) = N g := by simp [hk]
  by_cases hg : N g = 1
  · rw [globalizationLocalCoefficient_apply _ _ _ _ _ _ _ _ hg,
      globalizationLocalCoefficient_apply _ _ _ _ _ _ _ _ (hnorm.trans hg),
      mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
  · rw [globalizationLocalCoefficient_apply_of_ne_one _ _ _ _ _ _ _ _ hg,
      globalizationLocalCoefficient_apply_of_ne_one _ _ _ _ _ _ _ _ (hnorm ▸ hg)]

/-- The integral of any two-sided translate along a proper standard block radical vanishes.
Left invariance of Haar makes the linear functional on vectors factor through the zero
Jacquet quotient for the conjugated radical. -/
theorem globalizationLocalCoefficient_vanishing (hn : 0 < n) (ρ : Representation ℂ Aᵥ V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (z : V) :
    BaseChange.HasVanishingConstantTerms (globalizationLocalCoefficient v hn ρ hρ ℓ hℓ z) := by
  classical
  let R := v.adicCompletion K
  let : IsTopologicalGroup Aᵥ := (D).generalLinearTopologicalGroup n
  let : T2Space Aᵥ := (D).generalLinearT2Space n
  let : MeasurableSpace Aᵥ := borel _
  let : BorelSpace Aᵥ := ⟨rfl⟩
  intro B hB μ hμ
  let U := B.unipotentSubgroup R
  have hprop : B.parabolic R ≠ ⊤ := by
    intro htop
    have hs := CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top B htop
    have h0 := hs.elim (⟨0, by omega⟩ : Fin B.length) ⟨1, by omega⟩
    exact Nat.zero_ne_one (congrArg Fin.val h0)
  let c := globalizationLocalCoefficient v hn ρ hρ ℓ hℓ
  have hint (x y : Aᵥ) (s : V) : Integrable (fun u : U => c s (x * u.val * y)) μ := by
    let t := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)
    have ht : Topology.IsClosedEmbedding (fun u : U => t u.val) :=
      t.isClosedEmbedding.comp (B.isClosed_unipotentSubgroup R).isClosedEmbedding_subtypeVal
    exact ((c s).continuous.comp ht.continuous).integrable_of_hasCompactSupport
      ((c s).hasCompactSupport.comp_isClosedEmbedding ht)
  refine ⟨fun x y => hint x y z, fun x y => ?_⟩
  let L : V →ₗ[ℂ] ℂ :=
    { toFun s := ∫ u : U, c s (x * u.val * y) ∂μ
      map_add' s t := by
        simp only [map_add, Submodule.coe_add, Pi.add_apply, integral_add (hint x y s) (hint x y t)]
      map_smul' r s := by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        exact integral_const_mul r (fun u : U => c s (x * u.val * y)) }
  let W := B.conjugateUnipotent (F := R) x
  let : Subsingleton (Jacquet.Coinvariants ρ W) := hρ.2 B hprop x
  have hL (k : W) : L ∘ₗ ρ k = L := by
    ext s
    obtain ⟨u, hu, huk⟩ := k.property
    change MulAut.conj x u = k.val at huk
    let u₀ : U := ⟨u, hu⟩
    have hk : N k.val = 1 :=
      GeneralLinear.ker_determinant_le_ker_comp (D).normalizedAbsUnits
        (B.conjugateUnipotent_le_ker_determinant x k.property)
    change (∫ t : U, c (ρ k.val s) (x * t.val * y) ∂μ) = ∫ t : U, c s (x * t.val * y) ∂μ
    calc
      _ = ∫ t : U, c s (x * ((u₀⁻¹ * t).val) * y) ∂μ := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        rw [globalizationLocalCoefficient_translate v hn ρ hρ ℓ hℓ s k.val _ hk, ← huk,
          MulAut.conj_apply]
        simp [u₀, c, mul_assoc]
      _ = _ := integral_mul_left_eq_self (μ := μ) (fun t : U => c s (x * t.val * y)) u₀⁻¹
  have h := Jacquet.lift_mk ρ W L hL z
  rw [Subsingleton.elim (Jacquet.mk ρ W z) 0, map_zero] at h
  exact h.symm

end Langlands.TraceFormula
