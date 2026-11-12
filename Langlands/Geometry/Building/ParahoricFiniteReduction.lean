import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Langlands.Geometry.Building.ActualAffineRootLocalFiniteness
import Langlands.Geometry.Building.ChamberIwahoriProof

/-!
# Reduction of `U_{a,Ω,0}` and `P_Ω` to a finite subset of a bounded `Ω`

For `P : ParahoricBuildingData G`, a bounded `Ω ⊆ A(S)` and a point `x₀ ∈ Ω`, some finite
`Ω' ⊆ Ω` containing `x₀` has the same root fixers `U_{a,Ω',0} = U_{a,Ω,0}` for every relative
root `a`, hence the same groups `G(F)^♯_{Ω'} = G(F)^♯_Ω` and `P_{Ω'} = P_Ω`.

* `ParahoricBuildingData.exists_finite_subset_rootFixer_eq_of_mem`: one root at a time.
* `ParahoricBuildingData.exists_finite_subset_rootFixer_eq`: all roots at once.
* `ParahoricBuildingData.exists_finite_subset_parahoric_eq`: the consequence for `G(F)^♯` and
  `P_Ω`.
* `ParahoricFiniteReductionStatement` and its proof `parahoricFiniteReduction`: the root fixer
  reduction as a proposition over all supplied data.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- For `u ∈ U_a(F) ∖ {1}`, `u ∈ U_{a,y,0}` if and only if `ψ^u_a(y) ≥ 0`. -/
private theorem mem_filtration_zero_iff {α : relativeRoots P.i} {u : rationalPoints G}
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1) (y : P.Apartment) :
    u ∈ P.filtration y α 0 ↔ 0 ≤ P.reflectionFunctional α u y := by
  rw [KPApartmentData.mem_filtration, ← P.coe_reflectionFunctional_apply hu hu1 y,
    WithTop.coe_le_coe]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

/-- For a bounded `Ω`, a point `x₀ ∈ Ω` and a relative root `a`, some finite `Ω' ⊆ Ω`
containing `x₀` has `U_{a,Ω',0} = U_{a,Ω,0}`. The functionals `ψ^u_a` that are non-negative
at `x₀` but negative somewhere on `Ω` are bounded at `x₀`, hence finite in number; `Ω'` adds
to `x₀` one point of `Ω` where each of them is negative. -/
theorem exists_finite_subset_rootFixer_eq_of_mem {Ω : Set P.Apartment}
    (hb : P.IsBoundedSubset Ω) {x₀ : P.Apartment} (hx₀ : x₀ ∈ Ω) (α : relativeRoots P.i) :
    ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧ P.rootFixer α Ω' = P.rootFixer α Ω := by
  classical
  set φ := P.reflectionFunctional α 1 with hφ
  obtain ⟨M, hM⟩ := hb (-φ)
  -- A point of `Ω` where `ψ` is negative, if there is one.
  let w : (P.Apartment →ᵃ[ℝ] ℝ) → P.Apartment := fun ψ =>
    if h : ∃ x ∈ Ω, ψ x < 0 then h.choose else x₀
  have hw : ∀ ψ, w ψ ∈ Ω := by
    intro ψ
    simp only [w]
    split_ifs with h
    · exact h.choose_spec.1
    · exact hx₀
  have hwneg : ∀ ψ : P.Apartment →ᵃ[ℝ] ℝ, (∃ x ∈ Ω, ψ x < 0) → ψ (w ψ) < 0 := by
    intro ψ h
    simp only [w, h, ↓reduceDIte]
    exact h.choose_spec.2
  let T : Set (P.Apartment →ᵃ[ℝ] ℝ) :=
    {ψ | ∃ g ∈ P.rootGroup α, g ≠ 1 ∧ ψ = P.reflectionFunctional α g ∧
      |ψ x₀| ≤ |φ x₀| + |M|}
  have hT : T.Finite :=
    P.finite_bounded_reflectionFunctionals_of_oppositePairs P.hasOppositeFactorPairs α x₀ _
  have hsub : insert x₀ (w '' T) ⊆ Ω := by
    rintro _ (rfl | ⟨ψ, -, rfl⟩)
    exacts [hx₀, hw ψ]
  refine ⟨insert x₀ (w '' T), hsub, (hT.image w).insert x₀, Set.mem_insert _ _,
    le_antisymm ?_ (P.apartment.rootFixer_anti α hsub)⟩
  intro u hu
  rw [P.apartment.mem_rootFixer] at hu ⊢
  refine ⟨hu.1, fun x hx => ?_⟩
  by_cases hu1 : u = 1
  · rw [hu1]
    exact (P.filtration x α 0).one_mem
  rw [P.mem_filtration_zero_iff hu.1 hu1]
  by_contra hneg
  push Not at hneg
  set ψ := P.reflectionFunctional α u with hψ
  have h0 : 0 ≤ ψ x₀ := (P.mem_filtration_zero_iff hu.1 hu1 x₀).1 (hu.2 x₀ (Set.mem_insert _ _))
  -- `ψ - φ` is constant, so `ψ(x₀) < φ(x₀) - φ(x) ≤ φ(x₀) + M`.
  have hconst : ψ x - ψ x₀ = φ x - φ x₀ := by
    have e1 := ψ.linearMap_vsub x x₀
    have e2 := φ.linearMap_vsub x x₀
    rw [hψ, P.reflectionFunctional_linear] at e1
    rw [hφ, P.reflectionFunctional_linear] at e2
    rw [vsub_eq_sub] at e1 e2
    rw [← hψ] at e1
    rw [← hφ] at e2
    rw [← e1, ← e2]
  have hMx : -φ x ≤ M := hM ⟨x, hx, rfl⟩
  have hψT : ψ ∈ T := by
    refine ⟨u, hu.1, hu1, rfl, ?_⟩
    rw [abs_of_nonneg h0]
    linarith [le_abs_self (φ x₀), le_abs_self M]
  have hwψ := (P.mem_filtration_zero_iff hu.1 hu1 (w ψ)).1
    (hu.2 _ (Set.mem_insert_of_mem _ ⟨ψ, hψT, rfl⟩))
  linarith [hwneg ψ ⟨x, hx, hneg⟩]

/-- For a bounded `Ω` and `x₀ ∈ Ω`, some finite `Ω' ⊆ Ω` containing `x₀` has
`U_{a,Ω',0} = U_{a,Ω,0}` for every relative root `a`. -/
theorem exists_finite_subset_rootFixer_eq {Ω : Set P.Apartment} (hb : P.IsBoundedSubset Ω)
    {x₀ : P.Apartment} (hx₀ : x₀ ∈ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧
      ∀ α : relativeRoots P.i, P.rootFixer α Ω' = P.rootFixer α Ω := by
  classical
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  have : Finite (relativeRoots P.i) :=
    (P.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots P.i).to_subtype
  choose S hSΩ hSfin _ hSeq using
    fun α : relativeRoots P.i => P.exists_finite_subset_rootFixer_eq_of_mem hb hx₀ α
  have hsub : insert x₀ (⋃ α, S α) ⊆ Ω :=
    Set.insert_subset hx₀ (Set.iUnion_subset hSΩ)
  refine ⟨insert x₀ (⋃ α, S α), hsub, (Set.finite_iUnion hSfin).insert x₀,
    Set.mem_insert _ _, fun α => le_antisymm ?_ (P.apartment.rootFixer_anti α hsub)⟩
  rw [← hSeq α]
  exact P.apartment.rootFixer_anti α
    ((Set.subset_iUnion S α).trans (Set.subset_insert _ _))

/-- For a bounded `Ω` and `x₀ ∈ Ω`, some finite `Ω' ⊆ Ω` containing `x₀` has
`G(F)^♯_{Ω'} = G(F)^♯_Ω` and `P_{Ω'} = P_Ω`. -/
theorem exists_finite_subset_parahoric_eq {Ω : Set P.Apartment} (hb : P.IsBoundedSubset Ω)
    {x₀ : P.Apartment} (hx₀ : x₀ ∈ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧ P.sharpFixer Ω' = P.sharpFixer Ω ∧
      P.parahoric Ω' = P.parahoric Ω := by
  obtain ⟨Ω', hΩ', hfin, hx₀', heq⟩ := P.exists_finite_subset_rootFixer_eq hb hx₀
  have hsharp : P.sharpFixer Ω' = P.sharpFixer Ω := iSup_congr heq
  exact ⟨Ω', hΩ', hfin, hx₀', hsharp, by rw [parahoric, parahoric, hsharp]⟩

end ParahoricBuildingData

/-- For supplied Chapter 7 building data over a nonarchimedean local field, a bounded
`Ω ⊆ A(S)` and a point `x₀ ∈ Ω`, some finite `Ω' ⊆ Ω` containing `x₀` has
`U_{a,Ω',0} = U_{a,Ω,0}` for every relative root `a`. This replaces the increasing-union step
in the proof of KP Lemma 7.7.4 for bounded `Ω`. -/
def ParahoricFiniteReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Ω : Set P.Apartment), P.IsBoundedSubset Ω →
      ∀ x₀ ∈ Ω, ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧
        ∀ α : relativeRoots P.i, P.rootFixer α Ω' = P.rootFixer α Ω

/-- Proof of `ParahoricFiniteReductionStatement`. -/
theorem parahoricFiniteReduction : ParahoricFiniteReductionStatement.{u} :=
  fun _ _ _ _ _ _ _ P _ hb _ hx₀ => P.exists_finite_subset_rootFixer_eq hb hx₀

end Langlands.Geometry.Building
