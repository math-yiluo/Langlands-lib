import Langlands.LocalFactor.Abelian.EulerTestShells
import Langlands.BaseChange.PadicNormPullbackConductor

/-! # Conductor bounds for norm pullback and a finite family of twists -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField
open scoped BigOperators

universe u v uI

/-- Inversion preserves the conductor of a continuous multiplicative character. -/
theorem conductor_inv_eq {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) :
    letI := T.topology
    ∀ χ : Quasicharacter F.Carrier, T.multiplicativeConductor χ⁻¹ = T.multiplicativeConductor χ := by
  letI := T.topology
  exact Langlands.LocalFactor.PadicAbelian.multiplicativeConductor_inv_eq T

/-- A character of conductor at most `N` preserves nontriviality on
the principal units of level `N` when multiplied by another character. -/
theorem conductor_lt_mul_of_lt {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) :
    letI := T.topology
    ∀ (κ χ : Quasicharacter F.Carrier) (N : ℕ),
      T.multiplicativeConductor κ ≤ N → N < T.multiplicativeConductor χ →
      N < T.multiplicativeConductor (κ * χ) := by
  let := T.topology
  intro κ χ N hκ hχ
  obtain ⟨x, hx, hne⟩ := T.exists_nontrivial_below_multiplicativeConductor χ N hχ
  by_contra! h
  have hprod := (T.multiplicativeTrivialAt_iff_conductor_le _ _).mpr h x hx
  change κ x * χ x = 1 at hprod
  rw [(T.multiplicativeTrivialAt_iff_conductor_le _ _).mpr hκ x hx, one_mul] at hprod
  exact hne hprod

/-- A sufficiently ramified character of the lower field has sufficiently
ramified products with the finite family of characters and a sufficiently
ramified upper norm pullback, including their inverses. -/
def DeepNormTwistConductorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    letI := T.valuativeRel
    letI := S.valuativeRel
    ∀ (f d : ℕ), IsResidueDegree F.Carrier E.Carrier f → IsDifferentExponent F.Carrier E.Carrier d →
    ∀ (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
    ∀ (I : Type uI) [Fintype I] (ω : I → Quasicharacter F.Carrier) (B₁ B₂ : ℕ),
      ∃ N : ℕ, ∀ (χ : Quasicharacter F.Carrier), N < T.multiplicativeConductor χ →
        (∀ i : I, B₁ ≤ T.multiplicativeConductor (ω i * χ) ∧
          B₁ ≤ T.multiplicativeConductor (ω i * χ)⁻¹) ∧
        B₂ ≤ S.multiplicativeConductor (χ.comp (localNorm T S)) ∧
        B₂ ≤ S.multiplicativeConductor (χ.comp (localNorm T S))⁻¹

/-- Bound the conductor of the original character by the local sum over its
norm-trivial twists, and use the rank-one norm conductor formula. -/
theorem deepNormTwistConductors : DeepNormTwistConductorsStatement.{u, v, uI} := by
  intro p _ F E _ _ _ _ T S
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro f d hf hd A hA I _ ω B₁ B₂
  classical
  let N := max B₁ (max (∑ i : I, T.multiplicativeConductor (ω i)) (f * (B₂ + d)))
  refine ⟨N, fun χ hχ => ?_⟩
  have hfam (i : I) : T.multiplicativeConductor (ω i) ≤ N :=
    (Finset.single_le_sum (f := fun j : I => T.multiplicativeConductor (ω j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨fun i => ?_, ?_⟩
  · have h := (le_max_left _ _ : B₁ ≤ N).trans
      (conductor_lt_mul_of_lt T (ω i) χ N (hfam i) hχ).le
    exact ⟨h, by rwa [conductor_inv_eq T]⟩
  · obtain ⟨a, ha, hsum⟩ := padicNormPullbackConductor p F E T S χ f d hf hd A hA
    have hmem : (1 : F.Carrierˣ →* ℂˣ) ∈ A := (hA _).mpr fun _ => rfl
    obtain ⟨ξ, hξ, h₁⟩ := ha 1 hmem
    have heq : ξ = χ := by
      apply ContinuousMonoidHom.ext
      intro x
      have h := DFunLike.congr_fun hξ x
      change ξ x = 1 * χ x at h
      simpa only [one_mul] using h
    have h₁' : T.toLocalFieldData.multiplicativeConductor χ = a 1 := heq ▸ h₁
    rw [T.toLocalFieldData_multiplicativeConductor] at h₁'
    let η := χ.comp (localNorm T S)
    change (∑ κ ∈ A, a κ) = f * (S.toLocalFieldData.multiplicativeConductor η + d) at hsum
    rw [S.toLocalFieldData_multiplicativeConductor] at hsum
    have hχsum : T.multiplicativeConductor χ ≤ f * (S.multiplicativeConductor η + d) := by
      rw [h₁', ← hsum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    have hbound : f * (B₂ + d) < f * (S.multiplicativeConductor η + d) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hχ.trans_le hχsum)
    have hη : B₂ ≤ S.multiplicativeConductor η := by
      have h := lt_of_mul_lt_mul_left hbound (Nat.zero_le f)
      omega
    exact ⟨hη, by rwa [conductor_inv_eq S]⟩

end Langlands.BaseChange
