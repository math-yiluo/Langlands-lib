import Langlands.Representation.Archimedean.RealReverseTransfer
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# Annihilators for the `O(n)`-integration pairing

Let `ds` be a list of real blocks, `X` the `O(n)`-finite functions of the real standard module
of `ds` and `Y` the `O(n)`-finite functions of the principal series of the inverse position
characters of `ds`, paired by `⟨z, h⟩ = ∫_{O(n)} z(κ) h(κ) dκ`. For a subspace `V` of `Y` let
`perp ds V` be the functions `h ∈ X` with `⟨z, h⟩ = 0` for all `z ∈ V`.

* `isGKSubmodule_perp`: if `V` is a `(𝔤, K)`-submodule, `perp ds V` is a `(𝔤, K)`-submodule.
* `exists_eq_of_vanishing`: if `V` is stable under `O(n)` and `u ∈ Y` vanishes on
  `perp ds V`, then `u` agrees on `X` with some `z ∈ V`: `⟨u, h⟩ = ⟨z, h⟩` for all `h ∈ X`.

So the annihilator of `perp ds V` in `Y` is `V` plus the annihilator of `X`. The second item
rests on the relative version `mem_of_vanishing` of `KFiniteDual.mem_of_separating`: a finite
vector of the dual of an admissible representation of a compact group that vanishes on the
common kernel of a subrepresentation `G` of finite dual vectors lies in `G`.
-/

noncomputable section

open MeasureTheory

open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff MonoidAlgebra

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealPairingAnnihilator

open KFiniteDual

universe uK uV

/-! ## Relative separation for finite dual vectors -/

section Relative

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ K V} [IsSemisimpleModule ℂ[K] ρ.asModule]
  (hblock : ∀ c : Block ρ, FiniteDimensional ℂ (blockSub c).toSubmodule)
include hblock

/-- On a finite-dimensional block, a functional vanishing on the common kernel of a space `G`
of functionals agrees with a member of `G`. -/
theorem exists_mem_comp_proj_eq_of_vanishing (G : Submodule ℂ (Module.Dual ℂ V))
    (c : Block ρ) {ℓ : Module.Dual ℂ V} (hvan : ∀ v : V, (∀ w ∈ G, w v = 0) → ℓ v = 0) :
    ∃ w ∈ G, w ∘ₗ proj c = ℓ ∘ₗ proj c := by
  have := hblock c
  let r : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ (blockSub c).toSubmodule :=
    (blockSub c).toSubmodule.subtype.dualMap
  let D := G.map r
  have hmem : r ℓ ∈ D := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := D),
      Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hvan x fun w hw => hx (r w) (Submodule.mem_map_of_mem hw)
  obtain ⟨w, hw, hrw⟩ := hmem
  refine ⟨w, hw, LinearMap.ext fun v => ?_⟩
  exact LinearMap.congr_fun hrw (projTo c v)

/-- **Relative separation.** Let `G` be a subrepresentation of the dual consisting of finite
vectors. A finite vector of the dual that vanishes on the common kernel of `G` lies in `G`. -/
theorem mem_of_vanishing (G : Subrepresentation ρ.dual)
    (hG : ∀ w ∈ G, FiniteVectors.IsFiniteVector ρ.dual w) {ℓ : Module.Dual ℂ V}
    (hℓ : FiniteVectors.IsFiniteVector ρ.dual ℓ)
    (hvan : ∀ v : V, (∀ w ∈ G, w v = 0) → ℓ v = 0) : ℓ ∈ G := by
  rw [eq_sum_comp_proj hℓ]
  refine Submodule.sum_mem G.toSubmodule fun c _ => ?_
  obtain ⟨w, hw, hwc⟩ := exists_mem_comp_proj_eq_of_vanishing hblock G.toSubmodule c hvan
  rw [← hwc]
  exact FiniteVectors.orbitSpan_le ρ.dual w G hw (comp_proj_mem_orbitSpan c (hG w hw))

end Relative

/-! ## The integration pairing of a standard module with the dual principal series -/

open RealPrincipalSeriesDuality RealReverseTransfer RealStrictCharacterLanglandsQuotient
open JacquetKernel PartialJacquet Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceK_pa (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-- The functions of the `O(n)`-finite standard module of `ds` orthogonal to every function of
`V` for the pairing `⟨z, h⟩ = ∫_{O(n)} z(κ) h(κ) dκ`. -/
def perp (ds : List RealBlock)
    (V : Submodule ℂ (kFiniteFunctions
      (principalSeries ℝ n (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ n))) :
    Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :=
  (V.map (intPairing _ _ (fun _ ha => continuous_of_mem ha)
    (fun _ ha => continuous_of_mem_kFiniteFunctions ha))).dualCoannihilator

theorem mem_perp {ds : List RealBlock}
    {V : Submodule ℂ (kFiniteFunctions
      (principalSeries ℝ n (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ n))}
    (h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    h ∈ perp ds V ↔ ∀ z ∈ V,
      ∫ κ, (z : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
        (h : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0 := by
  rw [perp, Submodule.mem_dualCoannihilator]
  constructor
  · intro H z hz
    exact H _ (Submodule.mem_map_of_mem hz)
  · rintro H _ ⟨z, hz, rfl⟩
    exact H z hz

/-- Right derivatives move across the pairing with a sign. -/
theorem integral_rightDerivative_mul_add (ds : List RealBlock)
    (Y : Matrix (Fin n) (Fin n) ℝ) {z : Langlands.GeneralLinear n ℝ → ℂ}
    (hz : z ∈ principalSeries ℝ n (dualChar (realPositionCharacter ds)))
    {h : Langlands.GeneralLinear n ℝ → ℂ} (hh : h ∈ realStandardModule n ds)
    (hzc : Continuous (rightDerivative (matrixModel ℝ n) Y z))
    (hhc : Continuous (rightDerivative (matrixModel ℝ n) Y h)) :
    ∫ κ, rightDerivative (matrixModel ℝ n) Y z (κ : Langlands.GeneralLinear n ℝ) *
        h κ ∂haarK n +
      ∫ κ, z (κ : Langlands.GeneralLinear n ℝ) *
        rightDerivative (matrixModel ℝ n) Y h κ ∂haarK n = 0 := by
  have hhs := contMDiff_of_mem_realStandardModule hh
  have hhp := realStandardModule_le_principalSeries n ds hh
  rw [← integral_add (integrable_mul_of_continuous hzc hhs.continuous)
    (integrable_mul_of_continuous hz.1.continuous hhc)]
  rw [← integral_rightDerivative_eq_zero (contMDiff_mul_fun hz.1 hhs)
    (isModulusEquivariant_mul
      (fun i x => inv_mul_cancel₀ ((isSignedPower ds).ne_zero i x)) hz hhp) Y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact (rightDerivative_mul_fun hz.1 hhs Y _).symm

/-- **The orthogonal of a `(𝔤, K)`-submodule is a `(𝔤, K)`-submodule.** -/
theorem isGKSubmodule_perp (ds : List RealBlock)
    {V : Submodule ℂ (kFiniteFunctions
      (principalSeries ℝ n (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ n))}
    (hV : IsGKSubmodule (principalSeriesRep ℝ n (dualChar (realPositionCharacter ds)))
      (principalSeriesLie ℝ n (dualChar (realPositionCharacter ds))) V) :
    IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) (perp ds V) := by
  refine ⟨fun k h hh => ?_, fun X h hh => ?_⟩
  · rw [mem_perp] at hh ⊢
    intro z hz
    have h0 := hh _ (hV.1 k⁻¹ z hz)
    rw [principalSeriesRep_apply_coe, map_inv] at h0
    rw [realStandardRep_apply_coe, ← h0]
    have e := integral_translate_mul
      (k := (Unitary.toUnits k : Langlands.GeneralLinear n ℝ))
      (h : Langlands.GeneralLinear n ℝ → ℂ) (z : Langlands.GeneralLinear n ℝ → ℂ) k.2
    calc ∫ κ : unitaryCompact ℝ n, (z : Langlands.GeneralLinear n ℝ → ℂ) κ *
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (Unitary.toUnits k)
            (h : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n
        = ∫ κ : unitaryCompact ℝ n, (h : Langlands.GeneralLinear n ℝ → ℂ)
            ((κ : Langlands.GeneralLinear n ℝ) * Unitary.toUnits k) *
            (z : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n :=
          integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)
      _ = ∫ κ : unitaryCompact ℝ n, (h : Langlands.GeneralLinear n ℝ → ℂ) κ *
            (z : Langlands.GeneralLinear n ℝ → ℂ)
              ((κ : Langlands.GeneralLinear n ℝ) * (Unitary.toUnits k)⁻¹) ∂haarK n := e
      _ = _ := integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)
  · rw [mem_perp] at hh ⊢
    have hone : ∀ (Y : Matrix (Fin n) (Fin n) ℝ), ∀ z ∈ V,
        ∫ κ, (z : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
          ((realStandardLie n ds (1 ⊗ₜ Y) h : kFiniteFunctions (realStandardModule n ds)
            (unitaryCompact ℝ n)) : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0 := by
      intro Y z hz
      have hz' := hV.2 (1 ⊗ₜ Y) z hz
      have h0 := hh _ hz'
      have hsum := integral_rightDerivative_mul_add ds Y z.2.1 h.2.1
        (by
          rw [← principalSeriesLie_one_tmul_apply_coe]
          exact continuous_of_mem (principalSeriesLie ℝ n _ (1 ⊗ₜ Y) z).2)
        (by
          rw [← realStandardLie_one_tmul_apply_coe]
          exact continuous_of_mem_kFiniteFunctions (realStandardLie n ds (1 ⊗ₜ Y) h).2)
      rw [principalSeriesLie_one_tmul_apply_coe] at h0
      rw [realStandardLie_one_tmul_apply_coe]
      rw [h0, zero_add] at hsum
      exact hsum
    induction X using TensorProduct.inductionOn with
    | tmul c Y =>
        intro z hz
        have hcY : (c ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = c • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hcY, map_smul, LinearMap.smul_apply, Submodule.coe_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, hone Y z hz, mul_zero]
    | add X₁ X₂ h₁ h₂ =>
        intro z hz
        rw [map_add, LinearMap.add_apply, Submodule.coe_add]
        simp only [Pi.add_apply, mul_add]
        rw [integral_add
          (integrable_mul_of_continuous (continuous_of_mem z.2)
            (continuous_of_mem_kFiniteFunctions (realStandardLie n ds X₁ h).2))
          (integrable_mul_of_continuous (continuous_of_mem z.2)
            (continuous_of_mem_kFiniteFunctions (realStandardLie n ds X₂ h).2)),
          h₁ z hz, h₂ z hz, add_zero]

/-- **The annihilator of the orthogonal.** Let `V` be an `O(n)`-stable subspace of the
`O(n)`-finite dual principal series of `ds`, and `u` an `O(n)`-finite function of the dual
principal series with `⟨u, h⟩ = 0` for every `h` in `perp ds V`. Then there is `z ∈ V` with
`⟨u, h⟩ = ⟨z, h⟩` for every `h` of the `O(n)`-finite standard module of `ds`. -/
theorem exists_eq_of_vanishing (ds : List RealBlock)
    {V : Submodule ℂ (kFiniteFunctions
      (principalSeries ℝ n (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ n))}
    (hVK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ z ∈ V,
      principalSeriesRep ℝ n (dualChar (realPositionCharacter ds)) k z ∈ V)
    (u : kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ n))
    (hu : ∀ h ∈ perp ds V,
      ∫ κ, (u : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
        (h : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0) :
    ∃ z ∈ V, ∀ h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      ∫ κ, (u : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
          (h : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
        ∫ κ, (z : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
          (h : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n := by
  let D := kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
    (unitaryCompact ℝ n)
  let S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
  have hDc : ∀ a ∈ D, Continuous a := fun a ha => continuous_of_mem ha
  have hSc : ∀ a ∈ S, Continuous a := fun a ha => continuous_of_mem_kFiniteFunctions ha
  let Qd : D →ₗ[ℂ] Module.Dual ℂ S := intPairing D S hDc hSc
  have hQdK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (y : D),
      Qd (principalSeriesRep ℝ n (dualChar (realPositionCharacter ds)) k y) =
        (realStandardRep n ds).dual k (Qd y) := by
    intro k y
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply]
    change intPairing D S hDc hSc _ h = intPairing D S hDc hSc y _
    rw [intPairing_apply, intPairing_apply, principalSeriesRep_apply_coe,
      realStandardRep_apply_coe, map_inv]
    exact integral_translate_mul (k := (Unitary.toUnits k : Langlands.GeneralLinear n ℝ))
      _ _ k.2
  have hgk := isRealGKModule_realStandardModule n ds
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℝ] (realStandardRep n ds).asModule :=
    KFiniteDual.isSemisimpleModule hgk.1 hgk.2.1
  have hblock := KFiniteDual.finiteDimensional_block hgk.1 hgk.2.1 (realStandardAdmissible n ds)
  let G : Subrepresentation (realStandardRep n ds).dual :=
    { toSubmodule := V.map Qd
      apply_mem_toSubmodule := by
        rintro k _ ⟨z, hz, rfl⟩
        exact ⟨principalSeriesRep ℝ n (dualChar (realPositionCharacter ds)) k z, hVK k z hz,
          hQdK k z⟩ }
  have hG : ∀ w ∈ G, FiniteVectors.IsFiniteVector (realStandardRep n ds).dual w := by
    rintro _ ⟨z, -, rfl⟩
    exact isFiniteVector_dual_of_equivariant Qd hQdK
      ((isRealGKModule_principalSeries n (dualChar (realPositionCharacter ds))).1 z)
  have hvan : ∀ h : S, (∀ w ∈ G, w h = 0) → Qd u h = 0 := by
    intro h hh
    exact (intPairing_apply D S hDc hSc u h).trans
      (hu h ((mem_perp h).2 fun z hz => (intPairing_apply D S hDc hSc z h).symm.trans
        (hh _ ⟨z, hz, rfl⟩)))
  obtain ⟨z, hz, hzu⟩ := mem_of_vanishing hblock G hG
    (isFiniteVector_dual_of_equivariant Qd hQdK
      ((isRealGKModule_principalSeries n (dualChar (realPositionCharacter ds))).1 u)) hvan
  refine ⟨z, hz, fun h => ?_⟩
  have e := LinearMap.congr_fun hzu h
  rw [intPairing_apply, intPairing_apply] at e
  exact e.symm

end RealPairingAnnihilator

end Langlands.Archimedean
