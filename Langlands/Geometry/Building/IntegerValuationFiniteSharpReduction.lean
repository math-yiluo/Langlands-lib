import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.GenericZeroFixerNormalizerReduction

/-! # Bounded sharp fixers and conditional comparison for integer valuations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- Affine boundedness of an apartment subset. -/
def IsBoundedSubset (Ω : Set B.Apartment) : Prop :=
  ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)

/-- For `u ∈ U_a(F) ∖ {1}`, `u ∈ U_{a,y,0}` if and only if `ψ^u_a(y) ≥ 0`. -/
private theorem mem_filtration_zero_iff {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1) (y : B.Apartment) :
    u ∈ B.filtration y α 0 ↔ 0 ≤ B.reflectionFunctional α u y := by
  rw [KPApartmentData.mem_filtration, ← B.coe_reflectionFunctional_apply hu hu1 y,
    WithTop.coe_le_coe]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

/-- For a bounded `Ω`, a point `x₀ ∈ Ω` and a relative root `a`, some finite `Ω' ⊆ Ω`
containing `x₀` has `U_{a,Ω',0} = U_{a,Ω,0}`. The functionals `ψ^u_a` that are non-negative
at `x₀` but negative somewhere on `Ω` are bounded at `x₀`, hence finite in number; `Ω'` adds
to `x₀` one point of `Ω` where each of them is negative. -/
theorem exists_finite_subset_rootFixer_eq_of_mem {Ω : Set B.Apartment}
    (hb : B.IsBoundedSubset Ω) {x₀ : B.Apartment} (hx₀ : x₀ ∈ Ω) (α : relativeRoots B.i) :
    ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧ B.rootFixer α Ω' = B.rootFixer α Ω := by
  classical
  set φ := B.reflectionFunctional α 1 with hφ
  obtain ⟨M, hM⟩ := hb (-φ)
  -- A point of `Ω` where `ψ` is negative, if there is one.
  let w : (B.Apartment →ᵃ[ℝ] ℝ) → B.Apartment := fun ψ =>
    if h : ∃ x ∈ Ω, ψ x < 0 then h.choose else x₀
  have hw : ∀ ψ, w ψ ∈ Ω := by
    intro ψ
    simp only [w]
    split_ifs with h
    · exact h.choose_spec.1
    · exact hx₀
  have hwneg : ∀ ψ : B.Apartment →ᵃ[ℝ] ℝ, (∃ x ∈ Ω, ψ x < 0) → ψ (w ψ) < 0 := by
    intro ψ h
    simp only [w, h, ↓reduceDIte]
    exact h.choose_spec.2
  let T : Set (B.Apartment →ᵃ[ℝ] ℝ) :=
    {ψ | ∃ g ∈ B.rootGroup α, g ≠ 1 ∧ ψ = B.reflectionFunctional α g ∧
      |ψ x₀| ≤ |φ x₀| + |M|}
  have hT : T.Finite :=
    B.finite_bounded_reflectionFunctionals_of_oppositePairs B.hasOppositeFactorPairs α x₀ _
  have hsub : insert x₀ (w '' T) ⊆ Ω := by
    rintro _ (rfl | ⟨ψ, -, rfl⟩)
    exacts [hx₀, hw ψ]
  refine ⟨insert x₀ (w '' T), hsub, (hT.image w).insert x₀, Set.mem_insert _ _,
    le_antisymm ?_ (B.apartment.rootFixer_anti α hsub)⟩
  intro u hu
  rw [B.apartment.mem_rootFixer] at hu ⊢
  refine ⟨hu.1, fun x hx => ?_⟩
  by_cases hu1 : u = 1
  · rw [hu1]
    exact (B.filtration x α 0).one_mem
  rw [B.mem_filtration_zero_iff hu.1 hu1]
  by_contra hneg
  push Not at hneg
  set ψ := B.reflectionFunctional α u with hψ
  have h0 : 0 ≤ ψ x₀ := (B.mem_filtration_zero_iff hu.1 hu1 x₀).1 (hu.2 x₀ (Set.mem_insert _ _))
  -- `ψ - φ` is constant, so `ψ(x₀) < φ(x₀) - φ(x) ≤ φ(x₀) + M`.
  have hconst : ψ x - ψ x₀ = φ x - φ x₀ := by
    have e1 := ψ.linearMap_vsub x x₀
    have e2 := φ.linearMap_vsub x x₀
    rw [hψ, B.reflectionFunctional_linear] at e1
    rw [hφ, B.reflectionFunctional_linear] at e2
    rw [vsub_eq_sub] at e1 e2
    rw [← hψ] at e1
    rw [← hφ] at e2
    rw [← e1, ← e2]
  have hMx : -φ x ≤ M := hM ⟨x, hx, rfl⟩
  have hψT : ψ ∈ T := by
    refine ⟨u, hu.1, hu1, rfl, ?_⟩
    rw [abs_of_nonneg h0]
    linarith [le_abs_self (φ x₀), le_abs_self M]
  have hwψ := (B.mem_filtration_zero_iff hu.1 hu1 (w ψ)).1
    (hu.2 _ (Set.mem_insert_of_mem _ ⟨ψ, hψT, rfl⟩))
  linarith [hwneg ψ ⟨x, hx, hneg⟩]

/-- For a bounded `Ω` and `x₀ ∈ Ω`, some finite `Ω' ⊆ Ω` containing `x₀` has
`U_{a,Ω',0} = U_{a,Ω,0}` for every relative root `a`. -/
theorem exists_finite_subset_rootFixer_eq {Ω : Set B.Apartment} (hb : B.IsBoundedSubset Ω)
    {x₀ : B.Apartment} (hx₀ : x₀ ∈ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧
      ∀ α : relativeRoots B.i, B.rootFixer α Ω' = B.rootFixer α Ω := by
  classical
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : Finite (relativeRoots B.i) :=
    (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).to_subtype
  choose S hSΩ hSfin _ hSeq using
    fun α : relativeRoots B.i => B.exists_finite_subset_rootFixer_eq_of_mem hb hx₀ α
  have hsub : insert x₀ (⋃ α, S α) ⊆ Ω :=
    Set.insert_subset hx₀ (Set.iUnion_subset hSΩ)
  refine ⟨insert x₀ (⋃ α, S α), hsub, (Set.finite_iUnion hSfin).insert x₀,
    Set.mem_insert _ _, fun α => le_antisymm ?_ (B.apartment.rootFixer_anti α hsub)⟩
  rw [← hSeq α]
  exact B.apartment.rootFixer_anti α
    ((Set.subset_iUnion S α).trans (Set.subset_insert _ _))

/-- A bounded apartment subset has the same sharp fixer as a finite subset
containing any prescribed point of the original subset. -/
theorem exists_finite_subset_sharpFixer_eq {Ω : Set B.Apartment}
    (hb : B.IsBoundedSubset Ω) {x₀ : B.Apartment} (hx₀ : x₀ ∈ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Finite ∧ x₀ ∈ Ω' ∧ B.sharpFixer Ω' = B.sharpFixer Ω := by
  obtain ⟨Ω', hΩ', hfin, hx₀', heq⟩ := B.exists_finite_subset_rootFixer_eq hb hx₀
  exact ⟨Ω', hΩ', hfin, hx₀', iSup_congr heq⟩

/-- Extend the generic finite comparison to any nonempty affinely bounded subset. -/
theorem subgroup_pointwiseFixer_eq_trivialNormalizer_sup_sharpFixer_of_bounded
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints B.i))
    (hQ : ∀ n ∈ Q, ∀ x : B.Apartment, n • x = x)
    (hQH : Q.map (normalizerPoints B.i).subtype ≤ H)
    (hS : ∀ Ω : Set B.Apartment, B.sharpFixer Ω ≤ H)
    (hN : B.apartment.HasNormalizerSharpFixers H Q)
    {Ω : Set B.Apartment} (hne : Ω.Nonempty) (hb : B.IsBoundedSubset Ω) :
    H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) =
      Q.map (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨Ω', hsub, hfin, hx₀', hsharp⟩ := B.exists_finite_subset_sharpFixer_eq hb hx₀
  apply le_antisymm
  · calc
      H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) ≤
          H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω') :=
        inf_le_inf le_rfl (B.apartment.pointwiseFixer_image_anti hsub)
      _ = Q.map (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω := by
        rw [B.apartment.subgroup_pointwiseFixer_eq_trivialNormalizer_sup_sharpFixer_of_finite
          B.isConnectedReductive B.isMaximalSplitTorus H Q hQ hQH hS hN hfin ⟨x₀, hx₀'⟩]
        exact congrArg (fun L => Q.map (normalizerPoints B.i).subtype ⊔ L) hsharp
  · exact B.apartment.trivialNormalizer_sup_sharpFixer_le_subgroup_pointwiseFixer
      H Q hQ hQH hS Ω

/-- The whole-apartment constant-factor comparison, with its finite normalizer
premise explicit, for every nonempty affinely bounded subset. -/
theorem subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_bounded
    (H : Subgroup (rationalPoints G))
    (hS : ∀ Ω : Set B.Apartment, B.sharpFixer Ω ≤ H)
    (hN : B.apartment.HasNormalizerSharpFixers H
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker))
    {Ω : Set B.Apartment} (hne : Ω.Nonempty) (hb : B.IsBoundedSubset Ω) :
    H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) =
      (H ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ B.sharpFixer Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨Ω', hsub, hfin, hx₀', hsharp⟩ := B.exists_finite_subset_sharpFixer_eq hb hx₀
  apply le_antisymm
  · calc
      H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) ≤
          H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω') :=
        inf_le_inf le_rfl (B.apartment.pointwiseFixer_image_anti hsub)
      _ = (H ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ B.sharpFixer Ω := by
        rw [B.apartment.subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_finite
          B.isConnectedReductive B.isMaximalSplitTorus H hS hN hfin ⟨x₀, hx₀'⟩]
        exact congrArg (fun L =>
          (H ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ L) hsharp
  · exact sup_le
      (le_inf inf_le_left (inf_le_right.trans
        (B.apartment.pointwiseFixer_image_anti (Set.subset_univ Ω))))
      (le_inf (hS Ω) (B.apartment.sharpFixer_le_pointwiseFixer_image Ω))

end Langlands.Geometry.Building.IntegerValuationBuildingData
