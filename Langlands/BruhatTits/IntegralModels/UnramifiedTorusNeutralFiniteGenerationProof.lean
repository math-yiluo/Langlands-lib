import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationStatement
import Langlands.BruhatTits.IntegralModels.RelativeComponentFiniteIndex
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Torus.ConnectedReductive

/-! # Proof: torus points modulo neutral integral points are finitely generated -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

namespace UnramifiedTorusNeutralFiniteGeneration

section GroupTheory

variable {G : Type*} [Group G]

/-- For a homomorphism into the multiplicative form of a finitely generated abelian
group, finitely many elements together with the kernel generate the source. -/
theorem exists_finite_closure_sup_ker {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    (Φ : G →* Multiplicative A) :
    ∃ s : Set G, s.Finite ∧ Subgroup.closure s ⊔ Φ.ker = ⊤ := by
  let P : Submodule ℤ A := AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup' Φ.range)
  have hP : ∀ a : A, a ∈ P ↔ Multiplicative.ofAdd a ∈ Φ.range := fun a => Iff.rfl
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hmem : ∀ a : (S : Set A), ∃ g : G, Φ g = Multiplicative.ofAdd (a : A) := fun a =>
    (hP a).mp (by rw [← hS]; exact Submodule.subset_span a.2)
  choose f hf using hmem
  refine ⟨Set.range f, Set.finite_range f, ?_⟩
  rw [← codisjoint_iff, ← Subgroup.map_eq_range_iff]
  apply le_antisymm (Subgroup.map_le_range Φ _)
  rintro x ⟨g, rfl⟩
  have hx : Multiplicative.toAdd (Φ g) ∈ Submodule.span ℤ (S : Set A) := by
    rw [hS, hP]
    exact ⟨g, rfl⟩
  have key : ∀ a ∈ Submodule.span ℤ (S : Set A),
      Multiplicative.ofAdd a ∈ (Subgroup.closure (Set.range f)).map Φ := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact ⟨f ⟨a, ha⟩, Subgroup.subset_closure ⟨_, rfl⟩, hf _⟩
    | zero => exact one_mem _
    | add a b _ _ ha hb => exact mul_mem ha hb
    | smul n a _ ha =>
      rw [ofAdd_zsmul]
      exact zpow_mem ha n
  exact key _ hx

/-- A finite-index subgroup together with finitely many elements generates the group. -/
theorem exists_finite_closure_sup_eq_top (H : Subgroup G) [H.FiniteIndex] :
    ∃ s : Set G, s.Finite ∧ Subgroup.closure s ⊔ H = ⊤ := by
  refine ⟨Set.range (fun q : G ⧸ H => q.out), Set.finite_range _, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H x
  have hx : x = (x : G ⧸ H).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hx]
  exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨_, rfl⟩) (inv_mem h.2)

/-- The image of a finite-index subgroup, together with finitely many elements,
generates a subgroup containing the whole image. -/
theorem exists_finite_range_le_closure_sup_map {G' : Type*} [Group G'] (f : G' →* G)
    (H : Subgroup G') [H.FiniteIndex] :
    ∃ s : Set G, s.Finite ∧ f.range ≤ Subgroup.closure s ⊔ H.map f := by
  obtain ⟨s, hs, htop⟩ := exists_finite_closure_sup_eq_top H
  refine ⟨f '' s, hs.image f, ?_⟩
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, MonoidHom.map_closure]

end GroupTheory

/-- The dual of the rational character group of a torus is a finitely generated
`ℤ`-module. -/
theorem characterDual_finite {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    Module.Finite ℤ (rationalCharacters T →+ ℤ) := by
  obtain ⟨_, _⟩ := rationalCharacterLattice k T hT.isConnectedReductive_of_fieldSplitting
  exact Module.Finite.equiv (addMonoidHomLequivInt ℤ).symm

/-- The normalized integer valuation of the maximal unramified field and the
published spectral fixed-field valuation define the same character kernel. -/
theorem characterValuationKernel_maximalUnramified (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) :
    characterValuationKernel (MaximalUnramified.valuation F) T =
      characterValuationKernel (fixedFieldValuation F) T := by
  ext g
  simp only [mem_characterValuationKernel]
  exact forall_congr' fun _ => (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one

end UnramifiedTorusNeutralFiniteGeneration

open UnramifiedTorusNeutralFiniteGeneration in
/-- **Torus points modulo neutral integral points are finitely generated.** -/
theorem unramifiedTorusNeutralFiniteGeneration :
    UnramifiedTorusNeutralFiniteGenerationStatement.{u} := by
  intro F _ _ _ _ T hT D hD
  have := characterDual_finite hT
  obtain ⟨s₁, hs₁, h₁⟩ := exists_finite_closure_sup_ker
    (IntegerValuation.rationalCharacterValuation (MaximalUnramified.valuation F) T)
  obtain ⟨s₂, hs₂, h₂⟩ :=
    exists_finite_range_le_closure_sup_map D.full.integralPointMap D.neutralSections
  refine ⟨s₁ ∪ s₂, hs₁.union hs₂, ?_⟩
  rw [IntegerValuation.rationalCharacterValuation_ker,
    characterValuationKernel_maximalUnramified, ← hD] at h₁
  have h₂' : D.full.integralPoints ≤ Subgroup.closure s₂ ⊔ D.neutral.integralPoints := by
    rw [← D.neutralPoints_eq]
    exact h₂
  rw [eq_top_iff, ← h₁, Subgroup.closure_union, sup_assoc]
  exact sup_le_sup_left h₂' _

end Langlands.BruhatTits.IntegralModels
