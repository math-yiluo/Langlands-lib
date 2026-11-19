import Langlands.BushnellKutzko.SubfieldLayerLifting
import Langlands.BushnellKutzko.LatticeChainLayerIndicator

/-! # Endomorphism families from a single shift orbit -/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V) (E : Type uE) [Field E] [Algebra F E]
  [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E
local notation "kₑ[" F "," E "]" => ResidueField (subfieldIntegers F E)

section Orbit

variable (a : Eˣ) {t : ℤ} (ht : (𝓛.fieldShift E hE a).toAdd = t)

include ht in
private theorem subfieldOrbit_shift_pow (i : ℤ) (hi : t ∣ i) :
    i = 0 + 𝓛.stabilizerValuation (𝓛.subfieldStabilizer E hE (a ^ (i / t))) := by
  rw [subfieldStabilizer_shift, map_zpow, Int.toAdd_zpow, ht, zero_add, mul_comm,
    Int.ediv_mul_cancel hi]

/-- Translation from layer zero to a layer in its orbit under the given field unit. -/
def subfieldOrbitEquiv (i : ℤ) (hi : t ∣ i) : 𝓛.Layer 0 ≃ₗ[𝒪[F]] 𝓛.Layer i :=
  𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE (a ^ (i / t))) 0 i
    (𝓛.subfieldOrbit_shift_pow E hE a ht i hi)

/-- The transported endomorphism on the orbit of layer zero, with zero on other layers. -/
def subfieldOrbitFamily (D₀ : Module.End 𝒪[F] (𝓛.Layer 0)) (i : ℤ) :
    Module.End 𝒪[F] (𝓛.Layer i) :=
  if hi : t ∣ i then
    let p := 𝓛.subfieldOrbitEquiv E hE a ht i hi
    p.toLinearMap.comp (D₀.comp p.symm.toLinearMap)
  else 0

/-- At the initial index the transported family equals its given map. -/
@[simp] theorem subfieldOrbitFamily_zero (D₀ : Module.End 𝒪[F] (𝓛.Layer 0)) :
    𝓛.subfieldOrbitFamily E hE a ht D₀ 0 = D₀ := by
  rw [subfieldOrbitFamily, dite_eq_left (dvd_zero t)]
  apply LinearMap.ext
  intro q
  let p := 𝓛.subfieldOrbitEquiv E hE a ht 0 (dvd_zero t)
  have hp (w : 𝓛.Layer 0) : p w = w := by
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective 0 1 w
    change 𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE (a ^ (0 / t))) 0 0 _
        (𝓛.intervalMk 0 (0 + 1) v hv) = 𝓛.intervalMk 0 (0 + 1) v hv
    rw [stabilizerLayerEquiv_mk, intervalMk_eq_iff]
    simp
  have hs (w : 𝓛.Layer 0) : p.symm w = w := p.injective (by rw [p.apply_symm_apply, hp])
  change p (D₀ (p.symm q)) = D₀ q
  rw [hp, hs]

/-- Translation by the selected unit intertwines the transported family. -/
theorem subfieldOrbitFamily_commutes (ht₀ : 0 < t)
    (D₀ : Module.End 𝒪[F] (𝓛.Layer 0)) :
    a ∈ 𝓛.subfieldLayerCommutingSubgroup E hE (𝓛.subfieldOrbitFamily E hE a ht D₀) := by
  intro i j hij q
  have hjadd : j = i + t := hij.trans (congrArg (i + ·) ht)
  have hdiv : t ∣ j ↔ t ∣ i := hjadd ▸ dvd_add_left (dvd_refl t)
  by_cases hi : t ∣ i
  · have hj := hdiv.mpr hi
    rw [subfieldOrbitFamily, subfieldOrbitFamily, dite_eq_left hi, dite_eq_left hj]
    let p := 𝓛.subfieldOrbitEquiv E hE a ht i hi
    let p' := 𝓛.subfieldOrbitEquiv E hE a ht j hj
    let r := 𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE a) i j hij
    have hpow : a ^ (j / t) = a * a ^ (i / t) := by
      rw [hjadd, Int.add_ediv_of_dvd_left hi, Int.ediv_self ht₀.ne', zpow_add, zpow_one]
      exact mul_comm _ _
    have hcomp (w : 𝓛.Layer 0) : r (p w) = p' w := by
      obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective 0 1 w
      change 𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE a) i j hij
          (𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE (a ^ (i / t))) 0 i _
            (𝓛.intervalMk 0 (0 + 1) v hv)) =
        𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE (a ^ (j / t))) 0 j _
          (𝓛.intervalMk 0 (0 + 1) v hv)
      rw [stabilizerLayerEquiv_mk, stabilizerLayerEquiv_mk, stabilizerLayerEquiv_mk,
        intervalMk_eq_iff]
      simp only [subfieldStabilizer_apply, hpow, Units.val_mul, mul_smul, sub_self, zero_mem]
    obtain ⟨w, rfl⟩ := p.surjective q
    change r (p (D₀ (p.symm (p w)))) = p' (D₀ (p'.symm (r (p w))))
    rw [p.symm_apply_apply, hcomp, hcomp, p'.symm_apply_apply]
  · have hj : ¬ t ∣ j := fun h => hi (hdiv.mp h)
    simp only [subfieldOrbitFamily, dite_eq_right hi, dite_eq_right hj, LinearMap.zero_apply, map_zero]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsDiscreteValuationRing 𝒪ₑ[F,E]]

/-- Every residue scalar commuting with the initial endomorphism commutes with the transported family. -/
theorem mem_commutingResidueScalars_subfieldOrbitFamily (D₀ : Module.End 𝒪[F] (𝓛.Layer 0))
    (c : kₑ[F,E]) (hc :
      letI := 𝓛.subfieldLayerResidueModule E hE 0
      ∀ q : 𝓛.Layer 0, c • D₀ q = D₀ (c • q)) :
    c ∈ 𝓛.commutingResidueScalars E hE (𝓛.subfieldOrbitFamily E hE a ht D₀) := by
  intro i q
  let := 𝓛.subfieldLayerResidueModule E hE 0
  let := 𝓛.subfieldLayerResidueModule E hE i
  by_cases hi : t ∣ i
  · rw [subfieldOrbitFamily, dite_eq_left hi]
    let p := 𝓛.subfieldOrbitEquiv E hE a ht i hi
    obtain ⟨w, rfl⟩ := p.surjective q
    have hsmul (z : 𝓛.Layer 0) : p (c • z) = c • p z :=
      𝓛.subfieldLayerEquiv_residue_smul E hE _ (𝓛.subfieldOrbit_shift_pow E hE a ht i hi) c z
    change c • p (D₀ (p.symm (p w))) = p (D₀ (p.symm (c • p w)))
    rw [p.symm_apply_apply, ← hsmul, ← hsmul, p.symm_apply_apply, hc]
  · simp only [subfieldOrbitFamily, dite_eq_right hi, LinearMap.zero_apply, smul_zero]

end Orbit

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsDiscreteValuationRing 𝒪ₑ[F,E]]

include 𝓛 in
/-- The extension residue field is finite. -/
theorem finite_subfieldResidueField : Finite kₑ[F,E] := by
  have := 𝓛.finiteDimensional_subfield E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  exact Finite.of_equiv 𝓀[E] (ResidueField.mapEquiv (subfieldIntegerEquiv F E)).symm.toEquiv

/-- A proper residue subalgebra has an intertwining orbit family whose commuting
scalars do not contain the whole residue field. -/
theorem exists_subfieldOrbitFamily_of_ne_top (a : Eˣ) {t : ℤ}
    (ht : (𝓛.fieldShift E hE a).toAdd = t) (ht₀ : 0 < t)
    (S : Subalgebra 𝒪[F] kₑ[F,E]) (hS : S ≠ ⊤) :
    ∃ D : ∀ i, Module.End 𝒪[F] (𝓛.Layer i),
      a ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D ∧
      S ≤ 𝓛.commutingResidueScalars E hE D ∧
      𝓛.commutingResidueScalars E hE D ≠ ⊤ := by
  classical
  have := 𝓛.finite_subfieldResidueField E
  let := Fintype.ofFinite S
  let := Fintype.fieldOfDomain S
  let := 𝓛.subfieldLayerResidueModule E hE 0
  have := 𝓛.subfieldLayerResidueTower E hE 0
  have : IsScalarTower 𝒪[F] S (𝓛.Layer 0) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r q
    change (algebraMap 𝒪[F] kₑ[F,E] r) • q = r • q
    exact algebraMap_smul kₑ[F,E] r q
  have := 𝓛.layer_nontrivial 0
  obtain ⟨v, hv⟩ := exists_ne (0 : 𝓛.Layer 0)
  let f : S →ₗ[S] 𝓛.Layer 0 := LinearMap.id.smulRight v
  have hf : Function.Injective f := smul_left_injective S hv
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let D₀ : Module.End 𝒪[F] (𝓛.Layer 0) := (f.comp g).restrictScalars 𝒪[F]
  let D := 𝓛.subfieldOrbitFamily E hE a ht D₀
  use D, 𝓛.subfieldOrbitFamily_commutes E hE a ht ht₀ D₀
  constructor
  · intro c hc
    apply 𝓛.mem_commutingResidueScalars_subfieldOrbitFamily E hE a ht D₀ c
    intro q
    change (⟨c, hc⟩ : S) • (f.comp g) q = (f.comp g) ((⟨c, hc⟩ : S) • q)
    rw [map_smul]
  · intro h
    obtain ⟨c, hc⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hS)
    have hcv : c ∉ S := hc.2
    have htop : c ∈ (⊤ : Subalgebra 𝒪[F] kₑ[F,E]) := by simp
    have hC : c ∈ 𝓛.commutingResidueScalars E hE D := h.symm ▸ htop
    have hev : D₀ v = v := by
      have hg₁ : g (f 1) = 1 := LinearMap.congr_fun hg 1
      have hf₁ : f 1 = v := by simp [f]
      change f (g v) = v
      rw [← hf₁, hg₁]
    have hcv' := hC 0 v
    change c • D 0 v = D 0 (c • v) at hcv'
    have hm : D 0 = D₀ := 𝓛.subfieldOrbitFamily_zero E hE a ht D₀
    rw [hm, hev] at hcv'
    change c • v = (g (c • v) : S) • v at hcv'
    have heq : c = (g (c • v) : kₑ[F,E]) := smul_left_injective kₑ[F,E] hv hcv'
    exact hcv (heq.symm ▸ (g (c • v)).prop)

end Langlands.BushnellKutzko.LatticeChain
