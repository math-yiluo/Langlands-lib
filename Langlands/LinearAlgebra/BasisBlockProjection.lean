import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Block projections of a basis and their commutation with block-preserving maps -/

noncomputable section

open scoped Classical

namespace Langlands.LinearAlgebra.BasisBlockProjection

variable {R X I A : Type*} [CommRing R] [AddCommGroup X] [Module R X]
  (b : Module.Basis I R X) (θ : I → A)

/-- The projection onto the span of the basis vectors whose block is `α`, along the
remaining basis vectors. -/
def proj (α : A) : X →ₗ[R] X :=
  b.constr R (fun i => if θ i = α then b i else 0)

theorem proj_basis (α : A) (i : I) :
    proj b θ α (b i) = if θ i = α then b i else 0 := by
  simp [proj, Module.Basis.constr_basis]

/-- The coordinates of a block projection. -/
theorem repr_proj (α : A) (x : X) (i : I) :
    b.repr (proj b θ α x) i = if θ i = α then b.repr x i else 0 := by
  let g : X →ₗ[R] R := (b.coord i).comp (proj b θ α)
  let g' : X →ₗ[R] R := if θ i = α then b.coord i else 0
  have hg : g = g' := by
    apply b.ext
    intro j
    simp only [g, g', LinearMap.comp_apply, proj_basis]
    by_cases hj : θ j = α
    · by_cases hi : θ i = α
      · simp [hj, hi]
      · have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp [hj, hi, Module.Basis.coord_apply, Module.Basis.repr_self,
          hij.symm]
    · by_cases hi : θ i = α
      · have hij : j ≠ i := fun h => hj (h ▸ hi)
        simp [hj, hi, Module.Basis.coord_apply, Module.Basis.repr_self,
          hij]
      · simp [hj, hi]
  have := LinearMap.congr_fun hg x
  simp only [g, g', LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp [Module.Basis.coord_apply]

/-- The block projections over a finite set of blocks containing every block sum to
the identity. -/
theorem sum_proj (s : Finset A) (hs : ∀ i, θ i ∈ s) (x : X) :
    ∑ α ∈ s, proj b θ α x = x := by
  apply b.repr.injective
  ext i
  rw [map_sum, Finsupp.finsetSum_apply]
  simp only [repr_proj]
  rw [Finset.sum_ite_eq s (θ i) (fun _ => b.repr x i)]
  simp [hs i]

/-- A block projection vanishes exactly when the coordinates in its block vanish. -/
theorem proj_eq_zero_iff (α : A) (x : X) :
    proj b θ α x = 0 ↔ ∀ i, θ i = α → b.repr x i = 0 := by
  constructor
  · intro h i hi
    have := congrArg (fun y => b.repr y i) h
    simpa [repr_proj, hi] using this
  · intro h
    apply b.repr.injective
    ext i
    rw [repr_proj]
    split_ifs with hi
    · simp [h i hi]
    · simp

/-- A linear map that preserves, for every block, the vanishing of the coordinates in
that block commutes with every block projection. -/
theorem proj_comm (g : X →ₗ[R] X)
    (hg : ∀ (α : A) (x : X), (∀ i, θ i = α → b.repr x i = 0) →
      ∀ i, θ i = α → b.repr (g x) i = 0)
    (α : A) (x : X) :
    proj b θ α (g x) = g (proj b θ α x) := by
  set y := proj b θ α x with hy
  have hz : ∀ i, θ i = α → b.repr (x - y) i = 0 := by
    intro i hi
    rw [map_sub, Finsupp.sub_apply, hy, repr_proj]
    simp [hi]
  have hy' : ∀ α' ≠ α, ∀ i, θ i = α' → b.repr y i = 0 := by
    intro α' hα' i hi
    rw [hy, repr_proj]
    simp [show θ i ≠ α from hi ▸ hα']
  have hgz : proj b θ α (g (x - y)) = 0 :=
    (proj_eq_zero_iff b θ α _).mpr (hg α (x - y) hz)
  have hgy : proj b θ α (g y) = g y := by
    apply b.repr.injective
    ext i
    rw [repr_proj]
    split_ifs with hi
    · rfl
    · exact (hg (θ i) y (hy' (θ i) hi) i rfl).symm
  calc proj b θ α (g x) = proj b θ α (g (y + (x - y))) := by simp
    _ = proj b θ α (g y) + proj b θ α (g (x - y)) := by rw [map_add, map_add]
    _ = g y := by rw [hgy, hgz, add_zero]

end Langlands.LinearAlgebra.BasisBlockProjection
