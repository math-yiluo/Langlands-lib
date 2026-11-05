import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty

/-!
# Coefficient vanishing from Jacquet relations and uniform contraction

A finite set of genuine coinvariant relations controls each vector in the
Jacquet kernel. Uniform compact containment then gives coefficient vanishing
throughout a sufficiently small compatible-component epsilon chamber.
-/

noncomputable section

universe uR uG uV uW

namespace Langlands

section Algebraic

variable {R : Type uR} [CommRing R] {H : Type uG} [Group H]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]

/-- A finite set of radical elements suffices to annihilate a Jacquet relation
vector after translation, whenever their conjugates fix the output map. -/
theorem Jacquet.exists_finset_map_apply_eq_zero_of_mem_relations
    (ρ : Representation R H V) (N K : Subgroup H) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w)
    {v : V} (hv : v ∈ Jacquet.relations ρ N) :
    ∃ s : Finset N, ∀ g : H,
      (∀ n ∈ s, g * (n : H) * g⁻¹ ∈ K) → L (ρ g v) = 0 := by
  classical
  rw [Jacquet.relations_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨n, w⟩, rfl⟩ := hw
    refine ⟨{n}, fun g hg => ?_⟩
    have hk := hg n (Finset.mem_singleton_self n)
    have heq : g * (n : H) = (g * (n : H) * g⁻¹) * g := by group
    change L (ρ g (ρ (n : H) w - w)) = 0
    rw [map_sub, map_sub, sub_eq_zero]
    calc
      L (ρ g (ρ (n : H) w)) = L (ρ (g * (n : H)) w) := by
        rw [map_mul, Module.End.mul_apply]
      _ = L (ρ (g * (n : H) * g⁻¹) (ρ g w)) := by
        simpa only [map_mul, Module.End.mul_apply] using
          congrArg (fun z : H => L (ρ z w)) heq
      _ = L (ρ g w) := hL _ hk _
  | zero => exact ⟨∅, fun _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun g hg => ?_⟩
    rw [map_add, map_add, hs g (fun n hn => hg n (Finset.mem_union_left t hn)),
      ht g (fun n hn => hg n (Finset.mem_union_right s hn)), add_zero]
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, fun g hg => by rw [map_smul, map_smul, hs g hg, smul_zero]⟩

/-- A chosen finite radical witness for contraction of an individual relation
vector through a subgroup-invariant linear map. -/
def Jacquet.relationContractionWitness
    (ρ : Representation R H V) (N K : Subgroup H) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w)
    {v : V} (hv : v ∈ Jacquet.relations ρ N) : Finset N :=
  Classical.choose (Jacquet.exists_finset_map_apply_eq_zero_of_mem_relations ρ N K L hL hv)

/-- Conjugating the chosen witness into `K` annihilates the translated vector. -/
theorem Jacquet.relationContractionWitness_spec
    (ρ : Representation R H V) (N K : Subgroup H) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w)
    {v : V} (hv : v ∈ Jacquet.relations ρ N) (g : H)
    (hg : ∀ n ∈ Jacquet.relationContractionWitness ρ N K L hL hv,
      g * (n : H) * g⁻¹ ∈ K) :
    L (ρ g v) = 0 :=
  Classical.choose_spec
    (Jacquet.exists_finset_map_apply_eq_zero_of_mem_relations ρ N K L hL hv) g hg

end Algebraic

namespace BruhatTits.SpecialCompact

variable {R : Type uR} [CommRing R] {H : Type uG} [Group H] [TopologicalSpace H]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {K N Nbar : Subgroup H} {CAeps : ℝ → Set H}

/-- Uniform compact containment controls the finite relations of an individual
vector. Neither smoothness nor finite-dimensional fixed vectors are needed. -/
theorem UniformCompactContainment.exists_epsilon_map_apply_eq_zero
    (hC : UniformCompactContainment K N Nbar CAeps)
    (ρ : Representation R H V) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w)
    {v : V} (hv : v ∈ Jacquet.relations ρ N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ CAeps ε, L (ρ g v) = 0 := by
  obtain ⟨s, hs⟩ := Jacquet.exists_finset_map_apply_eq_zero_of_mem_relations ρ N K L hL hv
  obtain ⟨ε, hε, hcontain⟩ := hC.1 (s : Set N) s.finite_toSet.isCompact
  refine ⟨ε, hε, fun g hg => hs g fun n hn => ?_⟩
  have hn' : (n : H) ∈ ambientConjugate g⁻¹ ((K ⊓ N : Subgroup H) : Set H) :=
    hcontain g hg ⟨n, hn, rfl⟩
  obtain ⟨k, hk, heq⟩ := hn'
  have hconj : g * (n : H) * g⁻¹ = k := by
    rw [← heq]
    group
  rw [hconj]
  exact hk.1

/-- For a functional fixed by the dual `K`-action, every Jacquet relation
vector has zero coefficient on a sufficiently small epsilon chamber. -/
theorem UniformCompactContainment.exists_epsilon_matrixCoefficient_eq_zero
    (hC : UniformCompactContainment K N Nbar CAeps)
    (ρ : Representation R H V) (ℓ : Module.Dual R V)
    (hℓ : ℓ ∈ fixedVectors ρ.dual K)
    {v : V} (hv : v ∈ Jacquet.relations ρ N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ CAeps ε, matrixCoefficient ρ ℓ v g = 0 := by
  apply hC.exists_epsilon_map_apply_eq_zero ρ ℓ _ hv
  intro k hk w
  have h := congrArg (fun f : Module.Dual R V => f w) (hℓ ⟨k⁻¹, K.inv_mem hk⟩)
  change ℓ (ρ ((k⁻¹)⁻¹) w) = ℓ w at h
  simpa only [inv_inv] using h

end BruhatTits.SpecialCompact

end Langlands
