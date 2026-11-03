import Langlands.Representation.Jacquet.FixedVectorsGenerationStatement
import Langlands.Representation.Jacquet.CanonicalLiftDefinitions

/-! # Fixed-vector generation of actual Jacquet coinvariants -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Jacquet

universe uR uG uV

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- An element normalizing a subgroup preserves its fixed-vector module. -/
theorem apply_mem_fixedVectors_of_mem_normalizer (ρ : Representation R G V)
    (K : Subgroup G) {k : G} (hk : k ∈ Subgroup.normalizer K)
    {v : V} (hv : v ∈ fixedVectors ρ K) :
    ρ k v ∈ fixedVectors ρ K := by
  intro a
  have ha : k⁻¹ * (a : G) * k ∈ K :=
    (Subgroup.mem_normalizer_iff''.mp hk (a : G)).mp a.property
  change ρ (a : G) (ρ k v) = ρ k v
  rw [← Module.End.mul_apply, ← map_mul,
    show (a : G) * k = k * (k⁻¹ * (a : G) * k) by group,
    map_mul, Module.End.mul_apply]
  exact congrArg (ρ k) (hv ⟨_, ha⟩)

/-- The quotient of an ambient translate of a fixed vector lies in every
Jacquet subrepresentation containing the fixed vectors. -/
theorem mk_translate_mem_of_fixedVectors_le
    (ρ : Representation R G V) (N M K K₀ : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N)
    (hK₀ : K₀ ≤ Subgroup.normalizer K)
    (hfactor : ∀ g : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, g = m * n * k)
    (S : Subrepresentation (action ρ N M hMN))
    (hS : fixedVectors (action ρ N M hMN) (K.comap M.subtype) ≤ S.toSubmodule)
    {v : V} (hv : v ∈ fixedVectors ρ K) (g : G) :
    mk ρ N (ρ g v) ∈ S := by
  obtain ⟨m, hm, n, hn, k, hk, rfl⟩ := hfactor g
  have hkv := apply_mem_fixedVectors_of_mem_normalizer ρ K (hK₀ hk) hv
  have hq : mk ρ N (ρ k v) ∈
      fixedVectors (action ρ N M hMN) (K.comap M.subtype) :=
    (fixedJacquetMap ρ N M hMN K ⟨ρ k v, hkv⟩).property
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [← action_mk ρ N M hMN ⟨m, hm⟩, mk_apply_subgroup ρ N ⟨n, hn⟩]
  exact S.apply_mem_toSubmodule ⟨m, hm⟩ (hS hq)

/-- Fixed-vector generation descends to the actual unnormalized Jacquet
representation under the explicit normalizer and factorization hypotheses. -/
theorem fixedVectors_generate_of_factorization
    (ρ : Representation R G V) (N M K K₀ : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N)
    (hK₀ : K₀ ≤ Subgroup.normalizer K)
    (hfactor : ∀ g : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, g = m * n * k)
    (hgen : ∀ T : Subrepresentation ρ, fixedVectors ρ K ≤ T.toSubmodule → T = ⊤)
    (S : Subrepresentation (action ρ N M hMN))
    (hS : fixedVectors (action ρ N M hMN) (K.comap M.subtype) ≤ S.toSubmodule) :
    S = ⊤ := by
  let q := mk ρ N
  let C : Subrepresentation ρ :=
    { toSubmodule := ⨅ g, S.toSubmodule.comap (q.comp (ρ g))
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Submodule.mem_iInf] at hv ⊢
        intro a
        change q (ρ a (ρ g v)) ∈ S
        rw [← Module.End.mul_apply, ← map_mul]
        exact hv (a * g) }
  have hC : C = ⊤ := by
    apply hgen C
    intro v hv
    apply (Submodule.mem_iInf _).mpr
    intro g
    exact mk_translate_mem_of_fixedVectors_le ρ N M K K₀ hMN hK₀ hfactor S hS hv g
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := mk_surjective ρ N x
  have hv : v ∈ C := by rw [hC]; trivial
  have hv1 := (Submodule.mem_iInf _).mp hv 1
  change q (ρ 1 v) ∈ S at hv1
  simpa only [map_one, Module.End.one_apply] using hv1

/-- The complete algebraic fixed-vector generation statement, with three
independent universes. -/
theorem fixedVectorsGeneration :
    FixedVectorsGenerationStatement.{uR, uG, uV} := by
  intro R _ G _ V _ _ ρ N M K K₀ hMN hK₀ hfactor hgen S hS
  exact fixedVectors_generate_of_factorization ρ N M K K₀ hMN hK₀ hfactor hgen S hS

end Langlands.Jacquet
