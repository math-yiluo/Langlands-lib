import Langlands.GroupScheme.Reductive.TorusReynolds
import Langlands.GroupScheme.Reductive.FixedVectorRegularCoefficient

/-! # Normalized regular maps with diagonalizable-invariant image -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix

namespace Langlands.GroupScheme.AffineLinearEmbedding

variable {k B : Type*} [Field k] [AddCommGroup B] [Module k B] [Coalgebra k B]

/-- Left contraction is a morphism for the right regular coaction. -/
theorem comul_leftAct (θ : Module.Dual k B) (b : B) :
    Coalgebra.comul (R := k) (leftAct θ b) =
      (leftAct θ).rTensor B (Coalgebra.comul b) := by
  apply tensor_ext
  intro ψ
  change rightAct ψ (leftAct θ b) = _
  rw [rightAct_leftAct]
  have hc :
      (TensorProduct.rid k B).toLinearMap ∘ₗ ψ.lTensor B ∘ₗ (leftAct θ).rTensor B =
        leftAct θ ∘ₗ (TensorProduct.rid k B).toLinearMap ∘ₗ ψ.lTensor B := by
    ext x y
    simp
  exact (LinearMap.congr_fun hc (Coalgebra.comul b)).symm

end Langlands.GroupScheme.AffineLinearEmbedding

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Coordinates

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B] [Coalgebra k B]
  (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V)
  {n : Type} [Fintype n] [DecidableEq n]

omit [Coalgebra k B] [DecidableEq n] in
/-- Expanding the image of a coordinate matrix recovers the original linear combination. -/
theorem coactionCoordinates_mulVec_expand (a : n → B) (ha : ∀ j, a j ∈ V) (x : n → k) :
    ∑ l, (coactionCoordinates V b a *ᵥ x) l • (b l : B) =
      ∑ j, x j • a j := by
  calc
    _ = ∑ j, x j • ∑ l, extendedCoord V b l (a j) • (b l : B) := by
      simp only [coactionCoordinates, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by rw [mul_comm]
    _ = _ := Finset.sum_congr rfl fun j _ => by rw [basis_expand V b (ha j)]

end Coordinates

section Actual

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {Λ : Type u} [AddCommGroup Λ]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Apply the diagonalizable Reynolds projection to a normalized coefficient row. -/
def reynoldsCoefficientFamily
    (r : letI := bialgebra e
      B →ₐc[k] AddMonoidAlgebra k Λ)
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (i : n) : n → B := by
  let := bialgebra e
  exact fun j => diagonalizableReynolds r.toCoalgHom (normalizedCoefficientFamily e ρ v i j)

/-- Projection preserves the original coefficient-family coaction equation. -/
theorem reynoldsCoefficientFamily_comul
    (r : letI := bialgebra e
      B →ₐc[k] AddMonoidAlgebra k Λ)
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (i j : n) :
    letI := (bialgebra e).toCoalgebra
    comul (R := k) (reynoldsCoefficientFamily e r ρ v i j) =
      ∑ l, reynoldsCoefficientFamily e r ρ v i l ⊗ₜ[k]
        Unipotent.universalMatrix e ρ l j := by
  let := bialgebra e
  rw [reynoldsCoefficientFamily, diagonalizableReynolds, comul_leftAct,
    normalizedCoefficientFamily_comul, map_sum]
  simp only [LinearMap.rTensor_tmul]

/-- A nonzero fixed vector maps to one in a finite regular subspace whose every
coordinate satisfies the diagonalizable-invariance equation. -/
theorem exists_finite_diagonalizable_regular_map_to_one
    (r : letI := bialgebra e
      B →ₐc[k] AddMonoidAlgebra k Λ)
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    letI := (bialgebra e).toCoalgebra
    ∃ (V : Submodule k B) (d : ℕ) (b : Basis (Fin d) k V)
      (hV : ∀ (ψ : Module.Dual k B) (w : B), w ∈ V → rightAct ψ w ∈ V)
      (C : Matrix (Fin d) n k),
      Intertwines ρ (regularRepresentation e (Field.toIsField k) V b hV) C ∧
        (∀ w ∈ V, (r : B →ₗ[k] AddMonoidAlgebra k Λ).rTensor B (comul w) =
          (1 : AddMonoidAlgebra k Λ) ⊗ₜ[k] w) ∧
        ∑ l, (C *ᵥ v) l • (b l : B) = (1 : B) := by
  classical
  let := bialgebra e
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv0
  let a := normalizedCoefficientFamily e ρ v i
  let P := diagonalizableReynolds r.toCoalgHom
  let S : Finset B := Finset.univ.image a
  let U := regularSpan (K := k) S
  let V := U.map P
  let b := Module.finBasis k V
  have hU : ∀ (ψ : Module.Dual k B) (w : B), w ∈ U → rightAct ψ w ∈ U :=
    fun ψ _ hw => rightAct_mem_regularSpan S ψ hw
  have hV : ∀ (ψ : Module.Dual k B) (w : B), w ∈ V → rightAct ψ w ∈ V :=
    fun ψ _ hw => rightAct_mem_map_diagonalizableReynolds r.toCoalgHom U hU ψ hw
  have ha : ∀ j, P (a j) ∈ V := by
    intro j
    refine ⟨a j, subset_regularSpan S ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let C := coactionCoordinates V b (fun j => P (a j))
  refine ⟨V, Module.finrank k V, b, hV, C, ?_, ?_, ?_⟩
  · apply intertwines_of_universalMatrix e
    rw [regularRepresentation_universalMatrix]
    exact coactionCoordinates_mul V b (fun j => P (a j))
      (Unipotent.universalMatrix e ρ) ha (reynoldsCoefficientFamily_comul e r ρ v i)
  · rintro w ⟨z, _, rfl⟩
    exact diagonalizableReynolds_covariant r.toCoalgHom z
  · rw [coactionCoordinates_mulVec_expand V b _ ha]
    simp_rw [← P.map_smul]
    rw [← map_sum, normalizedCoefficientFamily_fixed e ρ v hv i hi]
    exact diagonalizableReynolds_one r

end Actual

end Langlands.GroupScheme.Chevalley
