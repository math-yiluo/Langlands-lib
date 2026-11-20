import Langlands.Global.Factors.RealIsobaricPlaceQuotient
import Langlands.Representation.Archimedean.RealStandardConstituentPermutation

/-!
# Reordering the real standard module while retaining its quotient

The operator constituent permutation theorem can be applied to a quotient
of the entire real standard module. Stability and equivariance for the real
matrix directions extend to the complexified Lie action by linearity.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean Langlands.Automorphic
open Langlands.Archimedean.ConstituentCompression

local notation "Matrices(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "LieSpace(" n ")" => ℂ ⊗[ℝ] Matrices(n)

private theorem stable_complexified {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : LieSpace(n) →ₗ⁅ℂ⁆ Module.End ℂ V} {W : Submodule ℂ V}
    (h : ∀ X : Matrices(n), ∀ x ∈ W, π (1 ⊗ₜ X) x ∈ W) :
    ∀ Z, ∀ x ∈ W, π Z x ∈ W := by
  intro Z
  induction Z using TensorProduct.inductionOn with
  | tmul c X =>
    intro x hx
    have hscalar : (c ⊗ₜ[ℝ] X : LieSpace(n)) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hscalar, map_smul, LinearMap.smul_apply]
    exact W.smul_mem c (h X x hx)
  | add X Y hX hY =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hX x hx) (hY x hx)

/-- The real constituent permutation theorem preserves the actual irreducible
quotient, with its compact and full complexified Lie actions. -/
theorem realStandardQuotientReordering : RealStandardQuotientReorderingStatement := by
  intro n ds xs hn hperm R hR hJ
  let ρ := (realStandardRep n ds).quotient R hR.1
  let π := RealLeviDuality.quotLie (realStandardLie n ds) R hR.2
  let L (X : Matrices(n)) := π (1 ⊗ₜ X)
  have := hJ.1
  have hsource : IsOperatorConstituent (realStandardOperators n ds) (Sum.elim (fun k => ρ k) L) := by
    refine ⟨⊤, fun _ _ _ => Submodule.mem_top, R.mkQ.comp (⊤ : Submodule ℂ _).subtype, ?_, ?_⟩
    · intro y
      obtain ⟨x, rfl⟩ := R.mkQ_surjective y
      exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
    · intro i x
      cases i <;> rfl
  obtain ⟨W, hW, q, hqsurj, hq⟩ := realStandardConstituent_perm ρ L hperm hn
    (fun U hK hL => hJ.2 U hK (stable_complexified hL)) hsource
  have hW' : IsGKSubmodule (realStandardRep n xs) (realStandardLie n xs) W :=
    ⟨fun k x hx => hW (.inl k) x hx, stable_complexified fun X x hx => hW (.inr X) x hx⟩
  let lieW := PlaceComponent.restrictLie hW'
  refine ⟨W, hW', q, hqsurj, fun k x => hq (.inl k) x, ?_⟩
  change ∀ Z x, q (lieW Z x) = π Z (q x)
  intro Z
  induction Z using TensorProduct.inductionOn with
  | tmul c X =>
    intro x
    have hscalar : (c ⊗ₜ[ℝ] X : LieSpace(n)) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hscalar]
    simp only [map_smul, LinearMap.smul_apply]
    exact congrArg (c • ·) (hq (.inr X) x)
  | add X Y hX hY =>
    intro x
    simp only [map_add, LinearMap.add_apply, hX, hY]

universe u

/-- Real generic standard parameters and tied irreducibility supply the
prescribed real-place quotient for every cuspidal family of the given rank. -/
def RealIsobaricPlaceQuotientReductionStatement : Prop :=
  RealGenericStandardParameterStatement.{u} → RealTemperedStandardIrreducibleStatement →
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ), ∑ i, (m i + 1) = r + 1 →
    ∀ (T : ∀ i, CuspidalOperatorRealization F (m i))
      (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}),
      HasRealIsobaricPlaceQuotient (r := r) T v

theorem realIsobaricPlaceQuotientReduction : RealIsobaricPlaceQuotientReductionStatement.{u} := by
  intro hparam htied F _ _ _ r k m hm T v
  exact hasRealIsobaricPlaceQuotient_of hparam htied realStandardQuotientReordering hm T v

end Langlands.Global
