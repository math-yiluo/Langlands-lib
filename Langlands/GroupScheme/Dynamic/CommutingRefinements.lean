import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.GroupScheme.Dynamic.NestedDecomposition

/-! # Common-Levi refinements of commuting dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.Dynamic

/-- Commutation of the images of two cocharacters is symmetric, on all tests. -/
theorem range_le_centralizer_symm {S : Scheme.{u}} {G : GroupScheme S}
    (χ τ : (Gm S).toGrp ⟶ G)
    (hτ : SubgroupFunctor.range τ ≤ centralizer χ) :
    SubgroupFunctor.range χ ≤ centralizer τ := by
  intro X g hg
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  rw [← torusCentralizer_gm_eq_dynamicCentralizer]
  intro Y a t
  rw [← Category.assoc]
  exact (commute_cocharacter_of_mem_centralizer χ
    (hτ Y (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)) (a ≫ s)).symm

/-- Exact all-test data for a refinement of the first cocharacter by the second.
The centralizer is the literal intersection of the original centralizers. -/
def IsCommutingRefinement {S : Scheme.{u}} {G : GroupScheme S}
    (χ τ ψ : (Gm S).toGrp ⟶ G) : Prop :=
  parabolic ψ ≤ parabolic χ ∧
    centralizer ψ = centralizer χ ⊓ centralizer τ ∧
    unipotent χ ≤ unipotent ψ ∧
    (∀ X : Over S,
      (↑((unipotent ψ).carrier X) : Set (X ⟶ G.X)) =
        (↑((centralizer χ ⊓ unipotent τ).carrier X) : Set (X ⟶ G.X)) *
          (↑((unipotent χ).carrier X) : Set (X ⟶ G.X))) ∧
    (∀ X : Over S,
      (↑((parabolic ψ).carrier X) : Set (X ⟶ G.X)) =
        (↑((centralizer χ ⊓ parabolic τ).carrier X) : Set (X ⟶ G.X)) *
          (↑((unipotent χ).carrier X) : Set (X ⟶ G.X)))

section Restriction

variable {S : Scheme.{u}} {G : GroupScheme S}
  (χ τ : (Gm S).toGrp ⟶ G)
  (hτ : SubgroupFunctor.range τ ≤ centralizer χ) (n : ℤ)

/-- The combination retains the second parabolic on the first centralizer. -/
theorem centralizer_inf_parabolic_combination :
    centralizer χ ⊓ parabolic (cocharacterCombination χ τ hτ n) =
      centralizer χ ⊓ parabolic τ := by
  apply SubgroupFunctor.ext
  intro X
  apply Subgroup.ext
  intro g
  change (g ∈ (centralizer χ).carrier X ∧
    ∃ e, IsOrbitExtension (cocharacterCombination χ τ hτ n) g e) ↔
      (g ∈ (centralizer χ).carrier X ∧ ∃ e, IsOrbitExtension τ g e)
  constructor
  · rintro ⟨hg, hp⟩
    exact ⟨hg, by simpa only [IsOrbitExtension,
      orbit_cocharacterCombination_of_mem_centralizer χ τ hτ n hg] using hp⟩
  · rintro ⟨hg, hp⟩
    exact ⟨hg, by simpa only [IsOrbitExtension,
      orbit_cocharacterCombination_of_mem_centralizer χ τ hτ n hg] using hp⟩

/-- The combination retains the second radical on the first centralizer. -/
theorem centralizer_inf_unipotent_combination :
    centralizer χ ⊓ unipotent (cocharacterCombination χ τ hτ n) =
      centralizer χ ⊓ unipotent τ := by
  apply SubgroupFunctor.ext
  intro X
  apply Subgroup.ext
  intro g
  change (g ∈ (centralizer χ).carrier X ∧
    HasLimit (cocharacterCombination χ τ hτ n) g 1) ↔
      (g ∈ (centralizer χ).carrier X ∧ HasLimit τ g 1)
  constructor
  · rintro ⟨hg, hp⟩
    exact ⟨hg, by simpa only [HasLimit, IsOrbitExtension,
      orbit_cocharacterCombination_of_mem_centralizer χ τ hτ n hg] using hp⟩
  · rintro ⟨hg, hp⟩
    exact ⟨hg, by simpa only [HasLimit, IsOrbitExtension,
      orbit_cocharacterCombination_of_mem_centralizer χ τ hτ n hg] using hp⟩

/-- The combination retains the second centralizer on the first centralizer. -/
theorem centralizer_inf_centralizer_combination :
    centralizer χ ⊓ centralizer (cocharacterCombination χ τ hτ n) =
      centralizer χ ⊓ centralizer τ := by
  apply SubgroupFunctor.ext
  intro X
  apply Subgroup.ext
  intro g
  change (g ∈ (centralizer χ).carrier X ∧
    g ∈ (centralizer (cocharacterCombination χ τ hτ n)).carrier X) ↔
      (g ∈ (centralizer χ).carrier X ∧ g ∈ (centralizer τ).carrier X)
  constructor
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    rw [mem_centralizer, orbit_cocharacterCombination_of_mem_centralizer χ τ hτ n hg]
      at hp
    exact hp
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    rw [mem_centralizer, orbit_cocharacterCombination_of_mem_centralizer χ τ hτ n hg]
    exact hp

/-- Once the dominant centralizer inclusion holds, its Levi is the literal
intersection of the two original centralizers. -/
theorem centralizer_combination_eq_inf
    (hZ : centralizer (cocharacterCombination χ τ hτ n) ≤ centralizer χ) :
    centralizer (cocharacterCombination χ τ hτ n) = centralizer χ ⊓ centralizer τ := by
  rw [← centralizer_inf_centralizer_combination χ τ hτ n]
  apply SubgroupFunctor.ext
  intro X
  exact (inf_eq_right.mpr (hZ X)).symm

variable [IsSeparated G.X.hom]

/-- The refined radical has the original coarse radical and the second
radical in the original centralizer as its exact same-test factors. -/
theorem unipotent_combination_eq_inter_mul
    (hP : parabolic (cocharacterCombination χ τ hτ n) ≤ parabolic χ)
    (hU : unipotent χ ≤ unipotent (cocharacterCombination χ τ hτ n)) (X : Over S) :
    (↑((unipotent (cocharacterCombination χ τ hτ n)).carrier X) : Set (X ⟶ G.X)) =
      (↑((centralizer χ ⊓ unipotent τ).carrier X) : Set (X ⟶ G.X)) *
        (↑((unipotent χ).carrier X) : Set (X ⟶ G.X)) := by
  rw [unipotent_eq_centralizer_inf_mul _ χ hP hU X,
    centralizer_inf_unipotent_combination χ τ hτ n]

/-- The refined parabolic is the exact product of the second parabolic in
the original centralizer and the original coarse radical. -/
theorem parabolic_combination_eq_inter_mul
    (hP : parabolic (cocharacterCombination χ τ hτ n) ≤ parabolic χ)
    (hU : unipotent χ ≤ unipotent (cocharacterCombination χ τ hτ n)) (X : Over S) :
    (↑((parabolic (cocharacterCombination χ τ hτ n)).carrier X) : Set (X ⟶ G.X)) =
      (↑((centralizer χ ⊓ parabolic τ).carrier X) : Set (X ⟶ G.X)) *
        (↑((unipotent χ).carrier X) : Set (X ⟶ G.X)) := by
  rw [parabolic_eq_centralizer_inf_mul _ χ hP
    (hU.trans (unipotent_le_parabolic _)) X,
    centralizer_inf_parabolic_combination χ τ hτ n]

end Restriction

section Existence

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsSeparated G.X.hom]
  (χ τ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (hτ : SubgroupFunctor.range τ ≤ centralizer χ)

include hτ

/-- A dominant commuting combination realizes the exact original
centralizer intersection and both original-point factorization formulas. -/
theorem exists_commuting_refinement :
    ∃ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      IsCommutingRefinement χ τ ψ := by
  obtain ⟨N, hN⟩ := exists_dominant_inclusions χ τ hτ
  let ψ := cocharacterCombination χ τ hτ (N : ℤ)
  obtain ⟨hP, hU, hZ⟩ := hN (N : ℤ) le_rfl ψ
    (fun _ t => comp_cocharacterCombination χ τ hτ (N : ℤ) t)
  exact ⟨ψ, hP, centralizer_combination_eq_inf χ τ hτ (N : ℤ) hZ, hU,
    unipotent_combination_eq_inter_mul χ τ hτ (N : ℤ) hP hU,
    parabolic_combination_eq_inter_mul χ τ hτ (N : ℤ) hP hU⟩

/-- Both orders admit refinements with exactly the same ambient centralizer.
Their exact radical and parabolic products are retained in the two data fields. -/
theorem exists_common_levi_refinements :
    ∃ ψ θ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      IsCommutingRefinement χ τ ψ ∧ IsCommutingRefinement τ χ θ ∧
        centralizer ψ = centralizer θ := by
  obtain ⟨ψ, hψ⟩ := exists_commuting_refinement χ τ hτ
  obtain ⟨θ, hθ⟩ := exists_commuting_refinement τ χ (range_le_centralizer_symm χ τ hτ)
  refine ⟨ψ, θ, hψ, hθ, ?_⟩
  rw [hψ.2.1, hθ.2.1]
  apply SubgroupFunctor.ext
  intro X
  exact inf_comm _ _

end Existence

end Langlands.GroupScheme.Dynamic
