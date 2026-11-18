import Langlands.GroupScheme.Reductive.FrobeniusSocleProducts
import Langlands.GroupScheme.Reductive.EigenMatrixCoefficient
import Langlands.GroupScheme.Reductive.CovariantConjugateTransport
import Langlands.GroupScheme.Reductive.CovariantCellFixedLine
import Langlands.GroupScheme.Reductive.AffineInducedRegular

/-! # Matrix coefficients against a covector as an embedding into a regular representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module TensorProduct
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance covectorRegularEmbeddingInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

variable {n : Type} [Fintype n] [DecidableEq n]

section Coefficient

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G), w ∈ V → rightAct ψ w ∈ V)

/-- An actual intertwiner into a finite regular representation, followed by the
coordinate map, is the matrix-coefficient map of the covector obtained by applying
the counit to the chosen basis and then the intertwiner. -/
theorem affineRegularCoordinateMap_mulVec_eq_matrixCoefficient
    {ρ : MatrixRepresentation G n} {C : Matrix (Fin d) n k}
    (hC : Intertwines ρ (affineRegularRepresentation G V b hV) C) (v : n → k) :
    affineRegularCoordinateMap G V b (C *ᵥ v) =
      matrixCoefficient G ρ
        ((fun i => counit (corepresentation G) (b i : algebra G)) ᵥ* C) v := by
  apply ext_pointAlgebraHom G
  intro T g
  rw [pointAlgebraHom_matrixCoefficient]
  have h := pointAlgebraHom_affineRegularCoordinateMap_mul G V b hV (C *ᵥ v) T 1 g
  rw [one_mul] at h
  rw [h]
  have hv : (fun j => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop ((C *ᵥ v) j)) =
      C.map (scalarMap T) *ᵥ fun j => scalarMap T (v j) := by
    funext j
    exact (scalarMap T).map_mulVec C v j
  have hM := hC.points T g
  have h1 : ∀ x, pointAlgebraHom G T 1 (b x : algebra G) =
      scalarMap T (counit (corepresentation G) (b x : algebra G)) := fun x => by
    rw [pointAlgebraHom_one_apply]
    rfl
  rw [Finset.sum_congr rfl fun x _ => by rw [h1 x]]
  rw [hv]
  have hξ : (fun i => scalarMap T (counit (corepresentation G) (b i : algebra G))) ᵥ*
      C.map (scalarMap T) = fun j => scalarMap T
        (((fun i => counit (corepresentation G) (b i : algebra G)) ᵥ* C) j) := by
    funext j
    exact ((scalarMap T).map_vecMul C _ j).symm
  change (fun i => scalarMap T (counit (corepresentation G) (b i : algebra G))) ⬝ᵥ
      (((affineRegularRepresentation G V b hV).pointMatrix T g :
        Matrix (Fin d) (Fin d) Γ(T.left, ⊤)) *ᵥ
        (C.map (scalarMap T) *ᵥ fun j => scalarMap T (v j))) = _
  rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hξ]
  rfl

end Coefficient

/-- For a nonzero covector `ξ` of an irreducible representation, the matrix coefficients
against `ξ` span a finite regular subspace, and the coordinates of these coefficients
give a bijective actual intertwiner onto its finite regular representation. -/
theorem exists_affineRegular_bijective_matrixCoefficient
    (ρ : MatrixRepresentation G n) (hρ : ρ.IsIrreducible) {ξ : n → k} (hξ : ξ ≠ 0) :
    ∃ (V : Submodule k (algebra G)) (d : ℕ) (b : Basis (Fin d) k V)
      (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
        ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G), w ∈ V → rightAct ψ w ∈ V)
      (C : Matrix (Fin d) n k),
      Intertwines ρ (affineRegularRepresentation G V b hV) C ∧
        Function.Bijective C.mulVecLin ∧
        ∀ v, affineRegularCoordinateMap G V b (C *ᵥ v) = matrixCoefficient G ρ ξ v := by
  classical
  let := (bialgebra (corepresentation G)).toCoalgebra
  let N := Unipotent.universalMatrix (corepresentation G)
    (ρ.restrict (groupSchemeIso G).hom)
  have hN : ∀ i j, AffineLinearEmbedding.comul (corepresentation G) (N i j) =
      ∑ l, N i l ⊗ₜ[k] N l j := fun i j => Unipotent.comul_universalMatrix _ _ i j
  have hNc : ∀ i j, AffineLinearEmbedding.counit (corepresentation G) (N i j) =
      (1 : Matrix n n k) i j := fun i j => Unipotent.counit_universalMatrix _ _ i j
  let a : n → algebra G := fun j => ∑ i, ξ i • N i j
  have ha_def : ∀ j, a j = ∑ i, ξ i • N i j := fun j => rfl
  have hcomul : ∀ j, Coalgebra.comul (R := k) (a j) = ∑ l, a l ⊗ₜ[k] N l j := by
    intro j
    change AffineLinearEmbedding.comul (corepresentation G) (a j) = _
    rw [ha_def, map_sum]
    have h2 : ∀ i, AffineLinearEmbedding.comul (corepresentation G) (ξ i • N i j) =
        ∑ l, (ξ i • N i l) ⊗ₜ[k] N l j := fun i => by
      rw [map_smul, hN]
      simp only [Finset.smul_sum, TensorProduct.smul_tmul']
    rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← TensorProduct.sum_tmul, ha_def]
  have hcounit : ∀ j, AffineLinearEmbedding.counit (corepresentation G) (a j) = ξ j := by
    intro j
    rw [ha_def, map_sum]
    simp only [map_smul, hNc, smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  let V := Submodule.span k (Set.range a)
  have ha : ∀ j, a j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hV : ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G), w ∈ V → rightAct ψ w ∈ V := by
    intro ψ
    have hle : V ≤ V.comap (rightAct ψ) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change rightAct ψ (a j) ∈ V
      rw [rightAct_apply, hcomul, map_sum, map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      exact V.smul_mem _ (ha l)
    exact fun w hw => hle hw
  have : Module.Finite k V := Module.Finite.span_of_finite k (Set.finite_range a)
  let b := Module.finBasis k V
  let C := coactionCoordinates V b a
  have hC' : Intertwines (ρ.restrict (groupSchemeIso G).hom)
      (regularRepresentation (corepresentation G) (Field.toIsField k) V b hV) C := by
    apply intertwines_of_universalMatrix (corepresentation G)
    rw [regularRepresentation_universalMatrix]
    exact coactionCoordinates_mul V b a N ha hcomul
  have hC : Intertwines ρ (affineRegularRepresentation G V b hV) C := by
    have h := hC'.restrict (groupSchemeIso G).inv
    rw [restrict_comp, Iso.inv_hom_id, restrict_id] at h
    exact h
  have hsum : ∀ c : n → k, affineRegularCoordinateMap G V b (C *ᵥ c) = ∑ j, c j • a j := by
    intro c
    rw [affineRegularCoordinateMap_apply]
    calc ∑ l, (C *ᵥ c) l • (b l : algebra G)
        = ∑ j, c j • ∑ l, extendedCoord V b l (a j) • (b l : algebra G) := by
          simp only [C, coactionCoordinates, Matrix.mulVec, dotProduct, Matrix.of_apply,
            Finset.sum_smul, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by
            rw [mul_comm]
      _ = ∑ j, c j • a j := Finset.sum_congr rfl fun j _ => by rw [basis_expand V b (ha j)]
  have hξC : (fun i => counit (corepresentation G) (b i : algebra G)) ᵥ* C = ξ := by
    funext j
    rw [← hcounit j, ← basis_expand V b (ha j), map_sum]
    simp only [Matrix.vecMul, dotProduct, C, coactionCoordinates, Matrix.of_apply, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hF : ∀ v, affineRegularCoordinateMap G V b (C *ᵥ v) = matrixCoefficient G ρ ξ v := by
    intro v
    rw [affineRegularCoordinateMap_mulVec_eq_matrixCoefficient G V b hV hC v, hξC]
  have hinj : Function.Injective C.mulVecLin := by
    apply hC.injective_of_isIrreducible hρ
    intro h0
    apply hξ
    funext j
    rw [← hcounit j]
    have h1 := hsum (Pi.single j 1)
    have h2 : C *ᵥ Pi.single j 1 = 0 := LinearMap.congr_fun h0 (Pi.single j 1)
    rw [h2, map_zero, Finset.sum_eq_single j
      (fun i _ hij => by rw [Pi.single_eq_of_ne hij, zero_smul]) (by simp),
      Pi.single_eq_same, one_smul] at h1
    rw [← h1, map_zero]
    rfl
  have hsurj : Function.Surjective C.mulVecLin := by
    intro x
    have hx : affineRegularCoordinateMap G V b x ∈ V := affineRegularCoordinateMap_mem G V b x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
    refine ⟨c, ?_⟩
    apply affineRegularCoordinateMap_injective G V b
    rw [Matrix.mulVecLin_apply, hsum, hc]
  exact ⟨V, Module.finrank k V, b, hV, C, hC, ⟨hinj, hsurj⟩, hF⟩

end Langlands.GroupScheme.Chevalley
