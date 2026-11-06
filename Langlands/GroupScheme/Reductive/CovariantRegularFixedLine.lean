import Langlands.GroupScheme.Reductive.CovariantCellFixedLine

/-! # Fixed lines in the actual finite regular representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)

/-- The coordinate function represented by a vector in the chosen basis of an
actual regular subspace. -/
def affineRegularCoordinateMap : (Fin d → k) →ₗ[k] algebra G :=
  V.subtype.comp b.equivFun.symm.toLinearMap

theorem affineRegularCoordinateMap_apply (v : Fin d → k) :
    affineRegularCoordinateMap G V b v = ∑ j, v j • (b j : algebra G) := by
  change ((b.equivFun.symm v : V) : algebra G) = _
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem affineRegularCoordinateMap_injective :
    Function.Injective (affineRegularCoordinateMap G V b) := by
  intro v w he
  exact b.equivFun.symm.injective (Subtype.ext he)

theorem affineRegularCoordinateMap_mem (v : Fin d → k) :
    affineRegularCoordinateMap G V b v ∈ V :=
  (b.equivFun.symm v).property

variable (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
  ∀ (f : Module.Dual k (algebra G)) (w : algebra G),
    w ∈ V → rightAct f w ∈ V)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a basis combination after right multiplication is evaluation
of the actual regular matrix acting on its scalar-extended coefficients. -/
theorem pointAlgebraHom_affineRegularCoordinateMap_mul
    (v : Fin d → k) (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X) :
    let M : Matrix (Fin d) (Fin d) ((algΓ (CommRingCat.of k)).obj T).unop :=
      ((affineRegularRepresentation G V b hV).pointMatrix T h :
        Matrix (Fin d) (Fin d) Γ(T.left, ⊤))
    pointAlgebraHom G T (g * h) (affineRegularCoordinateMap G V b v) =
      ∑ i, pointAlgebraHom G T g (b i : algebra G) *
        (M *ᵥ (fun j => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v j))) i := by
  dsimp only
  let M : Matrix (Fin d) (Fin d) ((algΓ (CommRingCat.of k)).obj T).unop :=
    ((affineRegularRepresentation G V b hV).pointMatrix T h :
      Matrix (Fin d) (Fin d) Γ(T.left, ⊤))
  rw [affineRegularCoordinateMap_apply, map_sum]
  calc
    _ = ∑ j, v j • ∑ i, pointAlgebraHom G T g (b i : algebra G) * M i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, affineRegularRepresentation_mul_basis G V b hV]
    _ = _ := by
      simp only [Algebra.smul_def, Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A fixed vector of the restricted actual regular representation represents
a function invariant on every original relative scheme test. -/
theorem affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector
    {U : GroupScheme (Spec (CommRingCat.of k))} (j : U ⟶ G)
    {v : Fin d → k}
    (hv : ((affineRegularRepresentation G V b hV).restrict j).IsFixedVector v) :
    affineRegularCoordinateMap G V b v ∈ rightInvariantSubspace j := by
  intro T u g
  rw [pointAlgebraHom_affineRegularCoordinateMap_mul G V b hV]
  have he := hv T u
  rw [pointMatrix_restrict] at he
  let M : Matrix (Fin d) (Fin d) ((algΓ (CommRingCat.of k)).obj T).unop :=
    ((affineRegularRepresentation G V b hV).pointMatrix T (u ≫ j.hom.hom) :
      Matrix (Fin d) (Fin d) Γ(T.left, ⊤))
  have he' : M *ᵥ (fun l => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v l)) =
      (fun l => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v l)) := he
  change ∑ i, pointAlgebraHom G T g (b i : algebra G) *
      (M *ᵥ (fun l => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v l))) i = _
  rw [he', affineRegularCoordinateMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Algebra.smul_def]
  exact mul_comm _ _

/-- A supplied normalized fixed vector spans the entire fixed space of the
actual regular representation on a covariant regular subspace, once the
supplied dense product cell determines invariant covariant functions. -/
theorem affineRegularRepresentation_fixedSubmodule_eq_span
    {H U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (i : H ⟶ G) (j : U ⟶ G) (χ : algebra H)
    (hcov : V ≤ AffineCoordinates.leftCovariantSubspace i χ)
    {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (v : Fin d → k)
    (hv : ((affineRegularRepresentation G V b hV).restrict j).IsFixedVector v)
    (hv1 : counit (corepresentation G) (affineRegularCoordinateMap G V b v) = 1) :
    ((affineRegularRepresentation G V b hV).restrict j).fixedSubmodule =
      Submodule.span k {v} := by
  have hvcov := hcov (affineRegularCoordinateMap_mem G V b v)
  have hvU := affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector G V b hV j hv
  apply le_antisymm
  · intro w hw
    have hwcov := hcov (affineRegularCoordinateMap_mem G V b w)
    have hwU := affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector G V b hV j hw
    have he := eq_counit_smul_of_covariant_rightInvariant i j χ hq hcell
      hvcov hvU hv1 hwcov hwU
    apply Submodule.mem_span_singleton.mpr
    refine ⟨counit (corepresentation G) (affineRegularCoordinateMap G V b w), ?_⟩
    apply affineRegularCoordinateMap_injective G V b
    rw [map_smul]
    exact he.symm
  · apply Submodule.span_le.mpr
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact hv

end Langlands.GroupScheme.Chevalley
