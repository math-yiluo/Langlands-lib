import Langlands.Representation.Character.CompressedTrace
import Langlands.Representation.Archimedean.GKModuleDensity

/-! # Finite-dimensional trace tests for archimedean algebraic modules -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.GKModuleDensity

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Group K] {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (σ : Representation ℂ K W) (τ : L →ₗ⁅ℂ⁆ Module.End ℂ W)

local notation "A" => FreeAlgebra ℂ (K ⊕ L)

/-- An algebraic `(𝔤, K)`-module as a module over the common algebra freely generated
by the compact operators and the infinitesimal operators. -/
@[instance_reducible]
def freeModule : Module A V := Module.compHom V (FreeAlgebra.lift ℂ (gens ρ π)).toRingHom

private theorem freeModule_isScalarTower :
    letI := freeModule ρ π
    IsScalarTower ℂ A V := by
  let _ := freeModule ρ π
  refine ⟨fun c a v => ?_⟩
  change FreeAlgebra.lift ℂ (gens ρ π) (c • a) v = c • FreeAlgebra.lift ℂ (gens ρ π) a v
  simp

private theorem isSimpleModule_freeModule (h : IsIrreducibleGKModule ρ π) :
    letI := freeModule ρ π
    IsSimpleModule A V := by
  let _ := freeModule ρ π
  let _ := freeModule_isScalarTower ρ π
  let _ := h.1
  have : IsSimpleOrder (Submodule A V) := by
    refine { eq_bot_or_eq_top := fun U => ?_ }
    let F := U.restrictScalars ℂ
    have hinv (a : K ⊕ L) (v : V) (hv : v ∈ F) : gens ρ π a v ∈ F := by
      have hs := U.smul_mem (FreeAlgebra.ι ℂ a) hv
      change FreeAlgebra.lift ℂ (gens ρ π) (FreeAlgebra.ι ℂ a) v ∈ U at hs
      change gens ρ π a v ∈ U
      simpa only [FreeAlgebra.lift_ι_apply] using hs
    obtain he | he := h.2 F (fun k v hv => hinv (.inl k) v hv) (fun X v hv => hinv (.inr X) v hv)
    · left
      ext v
      exact SetLike.ext_iff.mp he v
    · right
      ext v
      exact SetLike.ext_iff.mp he v
  exact ⟨⟩

variable {P Q : Type*} [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]
  [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q]

open Langlands.CharacterSeparation

/-- Equality of the two finite-dimensional trace tests on every word-polynomial in the
actual compact and Lie operators determines an irreducible algebraic module. -/
theorem exists_gkEquiv_of_compressedTrace_eq
    (hρ : IsIrreducibleGKModule ρ π) (hσ : IsIrreducibleGKModule σ τ)
    (i : P →ₗ[ℂ] V) (p : V →ₗ[ℂ] P) (j : Q →ₗ[ℂ] W) (q : W →ₗ[ℂ] Q)
    (hp : compressedTrace i p LinearMap.id ≠ 0)
    (h : ∀ a : A, compressedTrace i p (FreeAlgebra.lift ℂ (gens ρ π) a) =
      compressedTrace j q (FreeAlgebra.lift ℂ (gens σ τ) a)) :
    ∃ e : V ≃ₗ[ℂ] W, (∀ (k : K) (v : V), e (ρ k v) = σ k (e v)) ∧
      ∀ (X : L) (v : V), e (π X v) = τ X (e v) := by
  let _ := freeModule ρ π
  let _ := freeModule σ τ
  let _ := freeModule_isScalarTower ρ π
  let _ := freeModule_isScalarTower σ τ
  let _ := isSimpleModule_freeModule ρ π hρ
  let _ := isSimpleModule_freeModule σ τ hσ
  obtain ⟨e⟩ := nonempty_linearEquiv_of_compressedTrace_eq («A» := A) i p j q hp h
  refine ⟨e.restrictScalars ℂ, fun k v => ?_, fun X v => ?_⟩
  · have he := e.map_smul (FreeAlgebra.ι ℂ (Sum.inl k : K ⊕ L)) v
    change e (FreeAlgebra.lift ℂ (gens ρ π) (FreeAlgebra.ι ℂ (Sum.inl k)) v) =
      FreeAlgebra.lift ℂ (gens σ τ) (FreeAlgebra.ι ℂ (Sum.inl k)) (e v) at he
    rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply] at he
    exact he
  · have he := e.map_smul (FreeAlgebra.ι ℂ (Sum.inr X : K ⊕ L)) v
    change e (FreeAlgebra.lift ℂ (gens ρ π) (FreeAlgebra.ι ℂ (Sum.inr X)) v) =
      FreeAlgebra.lift ℂ (gens σ τ) (FreeAlgebra.ι ℂ (Sum.inr X)) (e v) at he
    rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply] at he
    exact he

end Langlands.Archimedean.GKModuleDensity
