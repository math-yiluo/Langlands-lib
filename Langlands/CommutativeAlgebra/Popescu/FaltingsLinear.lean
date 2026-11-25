import Langlands.MathlibBase

/-! # Injectivity of a base-changed linear map, tested on finite independent families -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open scoped TensorProduct

/-- A linear map sending a basis to a linearly independent family is injective. -/
theorem injective_of_basis {K M N ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (g : M →ₗ[K] N) (B : Module.Basis ι K M)
    (h : LinearIndependent K (g ∘ B)) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : Finsupp.linearCombination K (g ∘ B) (B.repr x) = 0 := by
    rw [← Finsupp.apply_linearCombination, B.linearCombination_repr, hx]
  have hrepr : B.repr x = 0 := linearIndependent_iff.mp h _ h0
  rw [← B.repr.map_eq_zero_iff]
  exact hrepr

/-- **Reduction to finite families.** Let `K/k` be a field extension, `f : V → W` a `k`-linear
map into a `K`-vector space and `S` a spanning set of `V`. If `f` sends every finite
`k`-linearly independent family of elements of `S` to a `K`-linearly independent family, then
`K ⊗_k V → W` is injective. -/
theorem liftBaseChange_injective_of_finite {k K V W : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module K W] [Module k W]
    [IsScalarTower k K W] (f : V →ₗ[k] W) (S : Set V) (hS : Submodule.span k S = ⊤)
    (h : ∀ (n : ℕ) (v : Fin n → V), (∀ i, v i ∈ S) → LinearIndependent k v →
      LinearIndependent K fun i => f (v i)) :
    Function.Injective (f.liftBaseChange K) := by
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent k S
  let B : Module.Basis b k V := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hS])
  have hB : ∀ i, B i = i.1 := fun i => Module.Basis.mk_apply hbli _ i
  apply injective_of_basis _ (B.baseChange K)
  have hcomp : (f.liftBaseChange K ∘ B.baseChange K) = fun i : b => f i.1 := by
    funext i
    rw [Function.comp_apply, Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul,
      one_smul, hB]
  rw [hcomp, linearIndependent_iff_finset_linearIndependent]
  intro s
  let e : Fin s.card ≃ s := s.equivFin.symm
  rw [← linearIndependent_equiv e]
  have hv := h s.card (fun i => (e i).1.1) (fun i => hbS (e i).1.2)
    (hbli.comp (fun i => (e i).1) (fun i j hij => e.injective (Subtype.ext hij)))
  exact hv

end Faltings

end Langlands.CommutativeAlgebra.Popescu
