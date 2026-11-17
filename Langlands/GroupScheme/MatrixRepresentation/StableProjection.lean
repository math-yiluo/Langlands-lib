import Langlands.GroupScheme.Chevalley.ActualRepresentationExtension
import Langlands.GroupScheme.Reductive.CovariantFrobeniusProducts
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Mathlib.LinearAlgebra.Projection

/-! # Actual restriction and equivariant stable projections -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- All-test stability is preserved by restriction along any actual morphism. -/
theorem IsStableSubspace.restrict {ρ : MatrixRepresentation G n}
    {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V) (f : H ⟶ G) :
    (ρ.restrict f).IsStableSubspace V := by
  intro A x v hv ℓ
  rw [affineMatrix_restrict]
  exact hV A (x ≫ f.hom.hom) v hv ℓ

/-- An actual group-scheme isomorphism preserves and reflects stable subspaces. -/
theorem isStableSubspace_restrict_iso_iff (ρ : MatrixRepresentation G n)
    (e : H ≅ G) (V : Submodule k (n → k)) :
    (ρ.restrict e.hom).IsStableSubspace V ↔ ρ.IsStableSubspace V := by
  constructor
  · intro h
    have h' := h.restrict e.inv
    simpa only [restrict_comp, e.inv_hom_id, restrict_id] using h'
  · exact fun h => h.restrict e.hom

/-- Equivariance can be checked after applying every ground-field linear
functional to the affine translates of ground-field vectors. -/
theorem intertwines_iff_linearFunctional_mulVec
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (C : Matrix m n k) :
    Intertwines ρ σ C ↔
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
        (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
        (v : n → k) (ℓ : A →ₗ[k] k),
        C *ᵥ (fun j => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
          (fun l => algebraMap k A (v l))) j)) =
          fun i => ℓ (((σ.affineMatrix A x : Matrix m m A) *ᵥ
            (fun l => algebraMap k A ((C *ᵥ v) l))) i) := by
  constructor
  · exact fun h => h.linearFunctional_mulVec
  · intro h A x
    have hvec (v : n → k) :
        C.map (algebraMap k A) *ᵥ
          ((ρ.affineMatrix A x : Matrix n n A) *ᵥ
            (fun j => algebraMap k A (v j))) =
        (σ.affineMatrix A x : Matrix m m A) *ᵥ
          (fun j => algebraMap k A ((C *ᵥ v) j)) := by
      ext i
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
      intro ℓ
      rw [map_sub, sub_eq_zero]
      have h' := h A x v ℓ
      rw [← linearFunctional_mulVec_rectangular] at h'
      exact congrFun h' i
    have hmap (v : n → k) :
        C.map (algebraMap k A) *ᵥ (fun j => algebraMap k A (v j)) =
          fun i => algebraMap k A ((C *ᵥ v) i) := by
      ext i
      exact ((algebraMap k A).map_mulVec C v i).symm
    apply Matrix.ext_of_mulVec_single
    intro j
    simp only [← Matrix.mulVec_mulVec]
    have hj : (fun l => algebraMap k A ((Pi.single j 1 : n → k) l)) =
        Pi.single j 1 := by
      ext l
      by_cases hl : l = j <;> simp [hl]
    have h' := hvec (Pi.single j 1)
    rw [← hmap, hj] at h'
    exact h'

/-- An equivariant projection is an actual intertwining linear endomorphism
whose image lies in the specified subspace and which fixes that subspace. -/
def IsEquivariantProjection (ρ : MatrixRepresentation G n)
    (V : Submodule k (n → k)) (P : Module.End k (n → k)) : Prop :=
  Intertwines ρ ρ (LinearMap.toMatrix' P) ∧ LinearMap.IsProj V P

/-- The usual projection along two stable complementary subspaces intertwines
the actual group-scheme representation, including on nonreduced tests. -/
theorem isEquivariantProjection_of_isCompl
    {ρ : MatrixRepresentation G n} {V W : Submodule k (n → k)}
    (hV : ρ.IsStableSubspace V) (hW : ρ.IsStableSubspace W) (hVW : IsCompl V W) :
    ρ.IsEquivariantProjection V (V.projection W hVW) := by
  refine ⟨?_, ⟨Submodule.projection_apply_mem hVW,
    fun v hv => Submodule.projection_apply_of_mem_left hVW hv⟩⟩
  apply (intertwines_iff_linearFunctional_mulVec _ _ _).mpr
  intro A x v ℓ
  simp only [LinearMap.toMatrix'_mulVec]
  have hv : v ∈ V ⊔ W := by rw [hVW.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hadd :
      (fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A ((a + b) j))) i)) =
      (fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (a j))) i)) +
      (fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (b j))) i)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hadd, map_add, Submodule.projection_apply_of_mem_left hVW (hV A x a ha ℓ),
    Submodule.projection_apply_of_mem_right hVW (hW A x b hb ℓ), add_zero,
    map_add, Submodule.projection_apply_of_mem_left hVW ha,
    Submodule.projection_apply_of_mem_right hVW hb, add_zero]

/-- An equivariant projection has a stable kernel complementary to its image. -/
theorem IsEquivariantProjection.stable_complement
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)}
    {P : Module.End k (n → k)} (hP : ρ.IsEquivariantProjection V P) :
    ρ.IsStableSubspace (LinearMap.ker P) ∧ IsCompl V (LinearMap.ker P) := by
  refine ⟨?_, hP.2.isCompl⟩
  have h := hP.1.isStableSubspace_ker
  have hmat : (LinearMap.toMatrix' P).mulVecLin = P := by
    apply LinearMap.ext
    intro v
    exact LinearMap.toMatrix'_mulVec P v
  simpa only [hmat] using h

/-- Stable complements of a stable subspace are equivalent to actual equivariant
projections onto it. -/
theorem exists_stable_complement_iff_exists_equivariantProjection
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)}
    (hV : ρ.IsStableSubspace V) :
    (∃ W : Submodule k (n → k), ρ.IsStableSubspace W ∧ IsCompl V W) ↔
      ∃ P : Module.End k (n → k), ρ.IsEquivariantProjection V P := by
  constructor
  · rintro ⟨W, hW, hVW⟩
    exact ⟨V.projection W hVW, isEquivariantProjection_of_isCompl hV hW hVW⟩
  · rintro ⟨P, hP⟩
    exact ⟨LinearMap.ker P, hP.stable_complement⟩

/-- An equivariant projection remains equivariant under any restriction. -/
theorem IsEquivariantProjection.restrict
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)}
    {P : Module.End k (n → k)} (hP : ρ.IsEquivariantProjection V P) (f : H ⟶ G) :
    (ρ.restrict f).IsEquivariantProjection V P :=
  ⟨hP.1.restrict f, hP.2⟩

end Langlands.GroupScheme.MatrixRepresentation
