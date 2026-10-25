import Langlands.GroupTheory.CyclicLatticeHerbrandStatement
import Langlands.Cohomology.HerbrandLattice

/-! # Cyclic Herbrand quotient invariance for full invariant real lattices -/

namespace Langlands.GroupTheory

open Langlands.Cohomology.Herbrand

universe v w

-- Use the canonical integer action on additive groups, as in `HerbrandLattice`.
attribute [-instance] ULift.module

/-- Pull a real basis back along an injective additive map whose image is its integer span. -/
private theorem exists_intBasis_of_range_eq_span
    {A : Type*} [AddCommGroup A] {V : Type*} [AddCommGroup V] [Module ℝ V]
    {κ : Type*} (b : Module.Basis κ ℝ V) (ι : A →+ V)
    (hinj : Function.Injective ι)
    (hrange : Set.range ι = (Submodule.span ℤ (Set.range b) : Set V)) :
    ∃ a : Module.Basis κ ℤ A, ∀ i, b i = ι (a i) := by
  classical
  let L := Submodule.span ℤ (Set.range b)
  let f : A →ₗ[ℤ] L := ι.toIntLinearMap.codRestrict L (fun x => by
    change ι x ∈ Submodule.span ℤ (Set.range b)
    exact (Set.ext_iff.mp hrange (ι x)).mp ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : V) ∈ Set.range ι := by
        rw [hrange]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  let e : A ≃ₗ[ℤ] L := LinearEquiv.ofBijective f hf
  let c : Module.Basis κ ℤ L := Module.Basis.span (b.linearIndependent.restrict_scalars' ℤ)
  refine ⟨c.map e.symm, fun i => ?_⟩
  change b i = ι (e.symm (c i))
  calc
    b i = (c i : V) := (Module.Basis.coe_span_apply _ i).symm
    _ = ι (e.symm (c i)) := (congrArg Subtype.val (e.apply_symm_apply (c i))).symm

/-- Milne VII Lemma 3.5, in the published basis-embedding formulation. -/
theorem cyclicLatticeHerbrandInvariance : CyclicLatticeHerbrandInvariance.{v,w} := by
  classical
  intro G _ _ _ V _ _ _ ρ M N ιM ιN hMinj hNinj hMeq hNeq hM hN hM1 hM2
  rcases hM with ⟨κ, aR, haR⟩
  rcases hN with ⟨κN, bR, hbR⟩
  let : Finite κ := Module.Finite.finite_basis aR
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨a, ha⟩ := exists_intBasis_of_range_eq_span aR ιM hMinj haR
  obtain ⟨b, hb⟩ := exists_intBasis_of_range_eq_span bR ιN hNinj hbR
  let e : κN ≃ κ := bR.indexEquiv aR
  let : Finite (groupCohomology M 1) := hM1
  let : Finite (groupCohomology M 2) := hM2
  obtain ⟨h₁, h₂, h⟩ :=
    (hasHerbrandQuotient_iff_of_bases (fun g => (ρ g).toLinearMap)
      a (b.reindex e) aR (bR.reindex e) ιM ιN ha
      (fun i => by simpa only [Module.Basis.reindex_apply] using hb (e.symm i))
      hMeq hNeq).1 (hasHerbrandQuotient_of_finite_cohomology M)
  refine ⟨h₁, h₂, ?_⟩
  have hM1pos : (Nat.card (groupCohomology M 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key : (Nat.card (groupCohomology M 2) : ℚ) * Nat.card (groupCohomology N 1) =
      Nat.card (groupCohomology N 2) * Nat.card (groupCohomology M 1) := by
    rw [h]
    field_simp
  exact_mod_cast key

end Langlands.GroupTheory
