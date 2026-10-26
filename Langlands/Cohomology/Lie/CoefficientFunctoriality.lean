import Langlands.Cohomology.Lie.CoefficientCochains
import Langlands.Representation.HorizontalAlternating

/-!
# Functoriality and full-group equivariance of coefficient cochains

Internal constructions from the published coefficient differential and actual
submodule of full-group-equivariant alternating maps.
-/

noncomputable section

namespace Langlands.Cohomology.Lie

open scoped BigOperators

universe u v v' v'' w w' w'' ug

variable {K : Type u} [Field K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {L' : Type v'} [LieRing L'] [LieAlgebra K L']
variable {L'' : Type v''} [LieRing L''] [LieAlgebra K L'']
variable {M : Type w} [AddCommGroup M] [Module K M]
variable {N : Type w'} [AddCommGroup N] [Module K N]
variable {P : Type w''} [AddCommGroup P] [Module K P]

/-- Pull back Lie-algebra arguments and postcompose coefficient values. -/
def pullMap (φ : L' →ₗ⁅K⁆ L) (ψ : M →ₗ[K] N) (q : ℕ) :
    Cochains K L M q →ₗ[K] Cochains K L' N q where
  toFun f := ψ.compAlternatingMap (f.compLinearMap φ.toLinearMap)
  map_add' f h := by
    apply AlternatingMap.ext
    intro x
    exact ψ.map_add _ _
  map_smul' a f := by
    apply AlternatingMap.ext
    intro x
    exact ψ.map_smul a _

@[simp] theorem pullMap_apply (φ : L' →ₗ⁅K⁆ L) (ψ : M →ₗ[K] N) (q : ℕ)
    (f : Cochains K L M q) (x : Fin q → L') :
    pullMap φ ψ q f x = ψ (f (fun i => φ (x i))) := rfl

@[simp] theorem pullMap_id (q : ℕ) :
    pullMap (LieHom.id : L →ₗ⁅K⁆ L) (LinearMap.id : M →ₗ[K] M) q =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply AlternatingMap.ext
  intro x
  rfl

/-- Lie-algebra maps compose contravariantly and coefficient maps covariantly. -/
theorem pullMap_comp (φ : L' →ₗ⁅K⁆ L) (φ' : L'' →ₗ⁅K⁆ L')
    (ψ : M →ₗ[K] N) (ψ' : N →ₗ[K] P) (q : ℕ) :
    pullMap (φ.comp φ') (ψ'.comp ψ) q =
      (pullMap φ' ψ' q).comp (pullMap φ ψ q) := by
  apply LinearMap.ext
  intro f
  apply AlternatingMap.ext
  intro x
  rfl

/-- Increasing deletion commutes with applying a Lie-algebra map. -/
theorem omitNth_lieHom (φ : L' →ₗ⁅K⁆ L) {q : ℕ}
    (i : Fin (q + 1)) (x : Fin (q + 1) → L') :
    omitNth i (fun j => φ (x j)) = fun j => φ (omitNth i x j) := rfl

/-- Bracket-first insertion commutes with a Lie-algebra map. -/
theorem bracketFirst_lieHom (φ : L' →ₗ⁅K⁆ L) {n : ℕ}
    (i j : Fin (n + 1)) (x : Fin (n + 2) → L') :
    bracketFirst i j (fun k => φ (x k)) = fun k => φ (bracketFirst i j x k) := by
  funext k
  refine Fin.cases ?_ (fun a => ?_) k
  · exact (φ.map_lie _ _).symm
  · rfl

section Differential

variable [CharZero K]
variable [LieRingModule L M] [LieModule K L M]
variable [LieRingModule L' N] [LieModule K L' N]

/-- Naturality for actual Lie maps and a compatible linear coefficient map. -/
theorem pullMap_differential (φ : L' →ₗ⁅K⁆ L) (ψ : M →ₗ[K] N)
    (hψ : ∀ x m, ψ ⁅φ x, m⁆ = ⁅x, ψ m⁆) (q : ℕ) (f : Cochains K L M q) :
    pullMap φ ψ (q + 1) (differential q f) = differential q (pullMap φ ψ q f) := by
  apply AlternatingMap.ext
  intro x
  cases q with
  | zero =>
    simp only [pullMap_apply, differential_apply_zero, hψ]
    exact congrArg (fun y : Fin 0 → L => ⁅x 0, ψ (f y)⁆) (Subsingleton.elim _ _)
  | succ n =>
    simp only [pullMap_apply, differential_apply_succ, map_add, map_sum, map_zsmul,
      omitNth_lieHom, bracketFirst_lieHom, hψ]

end Differential

section CoefficientMaps

variable [LieRingModule L M] [LieRingModule L N]

/-- The existing coefficient-map operation is the identity-argument specialization. -/
theorem pullMap_id_eq_map (ψ : M →ₗ⁅K,L⁆ N) (q : ℕ) :
    pullMap (LieHom.id : L →ₗ⁅K⁆ L) ψ.toLinearMap q = map ψ q := by
  apply LinearMap.ext
  intro f
  apply AlternatingMap.ext
  intro x
  rfl

end CoefficientMaps

section FullGroup

variable [CharZero K] [LieRingModule L M] [LieModule K L M]
variable {G : Type ug} [Group G]

/-- The constructed differential preserves equivariance for every group element. -/
theorem differential_mem_equivariant
    (σ : Representation K G L) (ρ : Representation K G M)
    (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
    (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
    (q : ℕ) (f : Cochains K L M q)
    (hf : f ∈ Langlands.HorizontalAlternating.equivariant σ ρ q) :
    differential q f ∈ Langlands.HorizontalAlternating.equivariant σ ρ (q + 1) := by
  intro g x
  cases q with
  | zero =>
    rw [differential_apply_zero, differential_apply_zero, hρ g]
    apply congrArg (fun m : M => ⁅σ g (x 0), m⁆)
    exact (congrArg f (Subsingleton.elim _ _)).trans (hf g Fin.elim0)
  | succ n =>
    let φ : L →ₗ⁅K⁆ L := { σ g with map_lie' := fun {a b} => hσ g a b }
    rw [differential_apply_succ, differential_apply_succ]
    simp only [map_add, map_sum, map_zsmul]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      apply congrArg (fun m : M => (-1 : ℤ) ^ (i : ℕ) • m)
      change ⁅σ g (x i), f (fun j => σ g (omitNth i x j))⁆ =
        ρ g ⁅x i, f (omitNth i x)⁆
      rw [hf g, hρ g]
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have ht : bracketFirst i j (fun k => σ g (x k)) =
          fun k => σ g (bracketFirst i j x k) := bracketFirst_lieHom φ i j x
      rw [ht, hf g]

/-- Actual linear restriction of the differential to full-group-equivariant cochains. -/
def equivariantDifferential
    (σ : Representation K G L) (ρ : Representation K G M)
    (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
    (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆) (q : ℕ) :
    Langlands.HorizontalAlternating.equivariant σ ρ q →ₗ[K]
      Langlands.HorizontalAlternating.equivariant σ ρ (q + 1) where
  toFun f := ⟨differential q f.val, differential_mem_equivariant σ ρ hσ hρ q f.val f.property⟩
  map_add' f h := Subtype.ext ((differential q).map_add f.val h.val)
  map_smul' a f := Subtype.ext ((differential q).map_smul a f.val)

@[simp] theorem equivariantDifferential_val
    (σ : Representation K G L) (ρ : Representation K G M)
    (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
    (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆) (q : ℕ)
    (f : Langlands.HorizontalAlternating.equivariant σ ρ q) :
    (equivariantDifferential σ ρ hσ hρ q f).val = differential q f.val := rfl

@[simp] theorem equivariantDifferential_apply
    (σ : Representation K G L) (ρ : Representation K G M)
    (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
    (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆) (q : ℕ)
    (f : Langlands.HorizontalAlternating.equivariant σ ρ q) (x : Fin (q + 1) → L) :
    (equivariantDifferential σ ρ hσ hρ q f).val x = differential q f.val x := rfl

end FullGroup

end Langlands.Cohomology.Lie
