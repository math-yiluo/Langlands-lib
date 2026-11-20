import Langlands.Representation.Archimedean.RealJacquetParameterSeparation

/-! # Real Jacquet functionals on a spherical principal series -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 100000

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.Archimedean.RealSphericalJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealCharacterCrossing (KF PL)
open RealJacquetParameterSeparation (evalOne exists_signMonomial_extension eq_zero_of_evalOne_rep)
open RealJacquetFiniteGeneration (Mat)

variable {n : ℕ}

/-- A spherical real principal series has a compact-fixed vector with value one at identity. -/
theorem exists_spherical (τ : Fin n → ℂ) :
    ∃ v : KF n (PL τ 0),
      (∀ k, realStandardRep n (PL τ 0) k v = v) ∧ evalOne (PL τ 0) v = 1 := by
  obtain ⟨v, hv⟩ := exists_signMonomial_extension τ 0
  have hvalue (k : Matrix.unitaryGroup (Fin n) ℝ) :
      (v : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) = 1 := by
    rw [hv]
    simp [JacquetNonvanishing.signMonomial, RealCharacterCrossing.pE]
  refine ⟨v, fun k => ?_, ?_⟩
  · apply Subtype.ext
    apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries
      (realStandardModule_le_principalSeries n (PL τ 0) (realStandardRep n (PL τ 0) k v).2.1)
      (realStandardModule_le_principalSeries n (PL τ 0) v.2.1)
    intro u hu
    let q : Matrix.unitaryGroup (Fin n) ℝ := ⟨(u : Mat n), hu⟩
    have hq : Unitary.toUnits q = u := RealSphericalCyclicProof.unitary_toUnits_mk hu
    rw [← hq, realStandardRep_apply_coe, TranslateFinite.rightTranslation_apply, ← map_mul,
      hvalue, hvalue]
  · change (v : Langlands.GeneralLinear n ℝ → ℂ) 1 = 1
    simpa only [map_one] using hvalue 1

/-- On a spherical real principal series in the closed chamber, a nonzero Jacquet functional
does not vanish on the spherical vector and has trivial signs. -/
theorem spherical_jacquet {τ : Fin n → ℂ} (hτ : Antitone fun i => (τ i).re)
    {v : KF n (PL τ 0)} (hvK : ∀ k, realStandardRep n (PL τ 0) k v = v) (hv₀ : v ≠ 0)
    {ℓ : KF n (PL τ 0) →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hℓ₀ : ℓ ≠ 0)
    (hℓ : IsRealJacquetFunctional n (realStandardRep n (PL τ 0)) (realStandardLie n (PL τ 0))
      ℓ a e) :
    ℓ v ≠ 0 ∧ e = 0 := by
  have hF : RealCharacterCrossing.frobMap hℓ v ≠ 0 := by
    intro hFv
    let ds := List.ofFn fun i => RealJacquetFrobenius.charData ((0 : Fin n → Fin 2) i) (τ i)
    have hlen : ds.length = n := List.length_ofFn
    have hpar : ∀ d ∈ ds, d.parity = 0 := by
      intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      rfl
    have hord : IsRealLanglandsOrdered (ds.map RealBlock.character) := by
      dsimp only [ds, IsRealLanglandsOrdered]
      rw [List.pairwise_map, List.pairwise_ofFn]
      intro i j hij
      exact hτ hij.le
    let F := RealCharacterCrossing.frobMap hℓ
    have hmem : v ∈ LinearMap.ker F := LinearMap.mem_ker.mpr hFv
    have hstable (X : ℂ ⊗[ℝ] Mat n) (w : KF n (PL τ 0))
        (hw : w ∈ LinearMap.ker F) : realStandardLie n (PL τ 0) X w ∈ LinearMap.ker F := by
      apply LinearMap.mem_ker.mpr
      change RealCharacterCrossing.frobMap hℓ (realStandardLie n (PL τ 0) X w) = 0
      rw [RealCharacterCrossing.frobMap_lie, show RealCharacterCrossing.frobMap hℓ w = 0 from
        LinearMap.mem_ker.mp hw, map_zero]
    have hker : LinearMap.ker F = ⊤ :=
      RealSphericalCyclicProof.realSphericalCyclic n ds hlen hpar hord v hvK hv₀
        (LinearMap.ker F) hmem hstable
    apply hℓ₀
    ext w
    have hw : w ∈ LinearMap.ker F := by rw [hker]; trivial
    rw [← RealCharacterCrossing.frobMap_apply_one hℓ w,
      show F w = 0 from LinearMap.mem_ker.mp hw]
    rfl
  have hvalue : ℓ v ≠ 0 := by
    intro hzero
    exact hF (eq_zero_of_evalOne_rep fun k => by
      rw [← RealCharacterCrossing.frobMap_rep, hvK]
      exact (RealCharacterCrossing.frobMap_apply_one hℓ v).trans hzero)
  refine ⟨hvalue, funext fun i => ?_⟩
  have hsign := (hℓ.2 i v).2
  rw [hvK] at hsign
  have hone : (-1 : ℂ) ^ (e i).val = 1 := by
    apply mul_right_cancel₀ hvalue
    rw [one_mul, ← hsign]
  have hi : e i = 0 ∨ e i = 1 := by omega
  rcases hi with h | h
  · exact h
  · norm_num [h] at hone

end Langlands.Archimedean.RealSphericalJacquet
