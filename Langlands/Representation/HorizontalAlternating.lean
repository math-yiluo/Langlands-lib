import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# Horizontal equivariant alternating maps

An internal linear-algebra construction for a represented module and a chosen
submodule. It includes every element of the acting group, without a connectedness
condition. No differential, Lie-module compatibility, or cohomology is asserted.
-/

noncomputable section

universe ur ug um uv uw uz

namespace Langlands.HorizontalAlternating

variable {R : Type ur} [CommRing R] {G : Type ug} [Group G]
  {M : Type um} [AddCommGroup M] [Module R M]
  {V : Type uv} [AddCommGroup V] [Module R V]
  {W : Type uw} [AddCommGroup W] [Module R W]
  {Z : Type uz} [AddCommGroup Z] [Module R Z]

/-- Alternating maps that vanish whenever any argument belongs to `H`. -/
def horizontal (H : Submodule R M) (q : ℕ) :
    Submodule R (M [⋀^Fin q]→ₗ[R] V) where
  carrier := {f | ∀ x i, x i ∈ H → f x = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' hf hg x i hi := by simp [hf x i hi, hg x i hi]
  smul_mem' a f hf x i hi := by simp [hf x i hi]

/-- The actual submodule of maps equivariant for every element of `G`. -/
def equivariant (σ : Representation R G M) (ρ : Representation R G V) (q : ℕ) :
    Submodule R (M [⋀^Fin q]→ₗ[R] V) where
  carrier := {f | ∀ g x, f (fun i => σ g (x i)) = ρ g (f x)}
  zero_mem' := by
    intro g x
    simp
  add_mem' hf hg g x := by simp [hf g x, hg g x]
  smul_mem' a f hf g x := by simp [hf g x]

/-- Horizontal maps satisfying full-group equivariance, as an actual intersection. -/
def submodule (H : Submodule R M) (σ : Representation R G M)
    (ρ : Representation R G V) (q : ℕ) : Submodule R (M [⋀^Fin q]→ₗ[R] V) :=
  horizontal H q ⊓ equivariant σ ρ q

@[simp] theorem mem_submodule (H : Submodule R M) (σ : Representation R G M)
    (ρ : Representation R G V) (q : ℕ) (f : M [⋀^Fin q]→ₗ[R] V) :
    f ∈ submodule H σ ρ q ↔
      (∀ x i, x i ∈ H → f x = 0) ∧
      (∀ g x, f (fun i => σ g (x i)) = ρ g (f x)) := Iff.rfl

variable (H : Submodule R M) (σ : Representation R G M)
  {ρ : Representation R G V} {τ : Representation R G W}
  {υ : Representation R G Z} (q : ℕ)

/-- Postcomposition by an actual coefficient intertwiner. -/
def mapCoefficients (A : Representation.IntertwiningMap ρ τ) :
    submodule H σ ρ q →ₗ[R] submodule H σ τ q where
  toFun f := ⟨A.toLinearMap.compAlternatingMap f.val, by
    constructor
    · intro x i hi
      change A (f.val x) = 0
      rw [f.property.1 x i hi, map_zero]
    · intro g x
      change A (f.val (fun i => σ g (x i))) = τ g (A (f.val x))
      rw [f.property.2 g x, A.isIntertwining]⟩
  map_add' f h := by
    apply Subtype.ext
    exact A.toLinearMap.compAlternatingMap_add _ _
  map_smul' a f := by
    apply Subtype.ext
    exact A.toLinearMap.compAlternatingMap_smul a _

@[simp] theorem mapCoefficients_apply (A : Representation.IntertwiningMap ρ τ)
    (f : submodule H σ ρ q) (x : Fin q → M) :
    (mapCoefficients H σ q A f).val x = A (f.val x) := rfl

@[simp] theorem mapCoefficients_id :
    mapCoefficients H σ q (Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  ext f
  rfl

@[simp] theorem mapCoefficients_comp (A : Representation.IntertwiningMap ρ τ)
    (B : Representation.IntertwiningMap τ υ) :
    mapCoefficients H σ q (B.comp A) =
      (mapCoefficients H σ q B).comp (mapCoefficients H σ q A) := by
  ext f
  rfl

theorem mapCoefficients_injective (A : Representation.IntertwiningMap ρ τ)
    (hA : Function.Injective A) : Function.Injective (mapCoefficients H σ q A) := by
  intro f h he
  apply Subtype.ext
  apply AlternatingMap.ext
  intro x
  apply hA
  exact congrArg (fun k : submodule H σ τ q => k.val x) he

/-- A coefficient representation equivalence transports the actual subspaces. -/
def coefficientEquiv (e : Representation.Equiv ρ τ) :
    submodule H σ ρ q ≃ₗ[R] submodule H σ τ q where
  __ := mapCoefficients H σ q e.toIntertwiningMap
  invFun := mapCoefficients H σ q e.symm.toIntertwiningMap
  left_inv f := by
    apply Subtype.ext
    ext x
    exact e.toLinearEquiv.symm_apply_apply (f.val x)
  right_inv f := by
    apply Subtype.ext
    ext x
    exact e.toLinearEquiv.apply_symm_apply (f.val x)

@[simp] theorem coefficientEquiv_apply (e : Representation.Equiv ρ τ)
    (f : submodule H σ ρ q) (x : Fin q → M) :
    (coefficientEquiv H σ q e f).val x = e (f.val x) := rfl

/-- In degree zero, horizontality is vacuous and equivariance means a fixed vector. -/
def degreeZeroEquiv (ρ : Representation R G V) :
    submodule H σ ρ 0 ≃ₗ[R] ρ.invariants where
  toFun f := ⟨f.val 0, by
    intro g
    have h := f.property.2 g (0 : Fin 0 → M)
    have hx : (fun i : Fin 0 => σ g ((0 : Fin 0 → M) i)) = 0 :=
      Subsingleton.elim _ _
    rw [hx] at h
    exact h.symm⟩
  invFun v := ⟨AlternatingMap.constOfIsEmpty R M (Fin 0) v.val, by
    constructor
    · intro x i
      exact Fin.elim0 i
    · intro g x
      exact (v.property g).symm⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    exact congrArg f.val (Subsingleton.elim (0 : Fin 0 → M) x)
  right_inv v := rfl
  map_add' f h := rfl
  map_smul' a f := rfl

@[simp] theorem degreeZeroEquiv_apply (ρ : Representation R G V)
    (f : submodule H σ ρ 0) : (degreeZeroEquiv H σ ρ f).val = f.val 0 := rfl

end Langlands.HorizontalAlternating
