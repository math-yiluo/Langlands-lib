import Langlands.Cohomology.PrimeMinimalPerfectProof
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Minimal local models with prescribed residue homology -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

/-- Over a local ring, a strictly perfect complex has a minimal finite free
homotopy model whose term ranks are its residue-field homology dimensions. -/
theorem exists_local_minimal_model
    (R : Type u) [CommRing R] [IsLocalRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : IsStrictlyPerfect K) :
    ∃ L : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteFree L ∧ Nonempty (HomotopyEquiv L K) ∧
      (∀ i j (x : L.X i),
        (L.d i j).hom x ∈ maximalIdeal R • (⊤ : Submodule R (L.X j))) ∧
      ∀ i : ℤ, Module.finrank R (L.X i) =
        Module.finrank (ResidueField R)
          (((baseChange (algebraMap R (ResidueField R))).obj K).homology i) := by
  obtain ⟨⟨a, b, ha, hb⟩, hterms⟩ := hK
  obtain ⟨L, hLa, hLb, hL, ⟨e⟩, hmin⟩ :=
    PrimeMinimal.exists_minimal_aux a b _ K ha hb hterms (Nat.lt_succ_self _)
  have hfree : ∀ i, Module.Finite R (L.X i) ∧ Module.Free R (L.X i) := by
    intro i
    obtain ⟨_, _⟩ := hL i
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  refine ⟨L, ⟨⟨a, b, hLa, hLb⟩, hfree⟩, ⟨e⟩, hmin, fun i ↦ ?_⟩
  let ρ := algebraMap R (ResidueField R)
  have hrank := PrimeMinimal.finrank_homology_baseChange ρ
    (fun r hr ↦ (residue_eq_zero_iff r).2 hr) hfree hmin i
  rw [← hrank]
  exact (baseChangeHomotopyEquiv ρ e).toHomologyIso i |>.toLinearEquiv.finrank_eq

/-- Residue homology supported in `[0,g]` and one-dimensional in degree zero
gives a minimal finite free homotopy model in that interval with rank-one
degree-zero term. -/
theorem exists_punctual_minimal_model
    (R : Type u) [CommRing R] [IsLocalRing R] (g : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : IsStrictlyPerfect K)
    (hvanish : ∀ i : ℤ, (i < 0 ∨ (g : ℤ) < i) →
      IsZero (((baseChange (algebraMap R (ResidueField R))).obj K).homology i))
    (hrank : Module.finrank (ResidueField R)
      (((baseChange (algebraMap R (ResidueField R))).obj K).homology 0) = 1) :
    ∃ L : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteFree L ∧ L.IsStrictlyGE 0 ∧ L.IsStrictlyLE (g : ℤ) ∧
      Nonempty (HomotopyEquiv L K) ∧ Nonempty (L.X 0 ≃ₗ[R] R) ∧
      ∀ i j (x : L.X i),
        (L.d i j).hom x ∈ maximalIdeal R • (⊤ : Submodule R (L.X j)) := by
  obtain ⟨L, hL, he, hmin, hdim⟩ := exists_local_minimal_model R K hK
  have hzero (i : ℤ) (hi : i < 0 ∨ (g : ℤ) < i) : IsZero (L.X i) := by
    obtain ⟨_, _⟩ := hL.2 i
    have := ModuleCat.subsingleton_of_isZero (hvanish i hi)
    have hdim0 : Module.finrank R (L.X i) = 0 := by
      rw [hdim i]
      exact Module.finrank_zero_of_subsingleton
    exact ModuleCat.isZero_iff_subsingleton.2
      ((Module.finrank_eq_zero_iff_of_free R (L.X i)).1 hdim0)
  refine ⟨L, hL, (CochainComplex.isStrictlyGE_iff L 0).2 (fun i hi ↦ hzero i (.inl hi)),
    (CochainComplex.isStrictlyLE_iff L (g : ℤ)).2 (fun i hi ↦ hzero i (.inr hi)),
    he, ?_, hmin⟩
  obtain ⟨_, _⟩ := hL.2 0
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one ((hdim 0).trans hrank)
  exact ⟨e.symm⟩

/-- A chosen minimal representative for the residue-amplitude reduction. -/
structure PunctualMinimalModel
    (R : Type u) [CommRing R] [IsLocalRing R] (g : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  finiteFree : IsFiniteFree complex
  strictlyGE : complex.IsStrictlyGE 0
  strictlyLE : complex.IsStrictlyLE (g : ℤ)
  equiv : HomotopyEquiv complex K
  zeroEquiv : complex.X 0 ≃ₗ[R] R
  minimal : ∀ i j (x : complex.X i),
    (complex.d i j).hom x ∈ maximalIdeal R • (⊤ : Submodule R (complex.X j))

/-- Choose a minimal finite free representative in degrees `[0,g]`. -/
def punctualMinimalModel
    (R : Type u) [CommRing R] [IsLocalRing R] (g : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : IsStrictlyPerfect K)
    (hvanish : ∀ i : ℤ, (i < 0 ∨ (g : ℤ) < i) →
      IsZero (((baseChange (algebraMap R (ResidueField R))).obj K).homology i))
    (hrank : Module.finrank (ResidueField R)
      (((baseChange (algebraMap R (ResidueField R))).obj K).homology 0) = 1) :
    PunctualMinimalModel R g K := by
  choose L hL hGE hLE e e₀ hmin using exists_punctual_minimal_model R g K hK hvanish hrank
  exact ⟨L, hL, hGE, hLE, e.some, e₀.some, hmin⟩

end Langlands.CommutativeAlgebra
