import Langlands.GroupScheme.Reductive.IntertwinerPolynomialPullback

/-! # Reducing conjugation maps to normalized finite regular representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

namespace MatrixLinear

variable {k : Type u} [CommRing k]
  {n r m : Type} [Fintype n] [Fintype r]

/-- Coefficients of a linear matrix map precomposed with a rectangular matrix. -/
def precomp (c : r → Matrix m m k) (C : Matrix r n k) : n → Matrix m m k :=
  fun j i l => ∑ a, c a i l * C a j

/-- Precomposition evaluates at the scalar-extended linear image. -/
theorem eval_precomp (c : r → Matrix m m k) (C : Matrix r n k)
    {A : Type*} [CommRing A] (f : k →+* A) (x : n → A) :
    eval (precomp c C) f x = eval c f (C.map f *ᵥ x) := by
  ext i l
  simp only [eval, precomp, map_sum, map_mul, Finset.sum_mul, Matrix.mulVec,
    dotProduct, Matrix.map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

end MatrixLinear

namespace MatrixRepresentation.ConjugationLinearMap

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n r m : Type} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
  {ρ : MatrixRepresentation G n} {τ : MatrixRepresentation G r}
  {σ : MatrixRepresentation G m}

/-- Precompose a conjugation map with an actual intertwiner of an affine group. -/
def precomp [IsAffine G.X.left] (φ : ConjugationLinearMap τ σ)
    {C : Matrix r n k} (hC : Intertwines ρ τ C) : ConjugationLinearMap ρ σ where
  coeff := MatrixLinear.precomp φ.coeff C
  equivariant T g x := by
    rw [MatrixLinear.eval_precomp, MatrixLinear.eval_precomp, Matrix.mulVec_mulVec,
      hC.points T g, ← Matrix.mulVec_mulVec]
    exact φ.equivariant T g _

/-- A nonzero scalar identity image gives a positive-degree invariant separator. -/
theorem exists_invariant_polynomial_of_scalar [Nonempty m]
    (φ : ConjugationLinearMap ρ σ) (v : n → k) {a : k} (ha : a ≠ 0)
    (hφ : MatrixLinear.eval φ.coeff (RingHom.id k) v =
      a • (1 : Matrix m m k)) :
    ∃ (d : ℕ) (F : MvPolynomial n k), 0 < d ∧ F.IsHomogeneous d ∧
      ρ.IsInvariantPolynomial F ∧ MvPolynomial.eval v F ≠ 0 := by
  apply φ.exists_invariant_polynomial v
  rw [hφ, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ ha

end MatrixRepresentation.ConjugationLinearMap

namespace Chevalley

open AffineLinearEmbedding MatrixRepresentation Module

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

/-- To construct conjugation maps for all fixed vectors, it suffices to construct
them for the constant-one vectors in finite regular representations. -/
theorem exists_conjugation_map_of_affine_regular
    (hregular :
      ∀ (V : Submodule k (AffineCoordinates.algebra G)) (d : ℕ) (b : Basis (Fin d) k V)
        (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
          ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
            w ∈ V → rightAct f w ∈ V)
        (w : Fin d → k),
        (affineRegularRepresentation G V b hV).IsFixedVector w →
        (∑ l, w l • (b l : AffineCoordinates.algebra G)) = 1 →
        ∃ (m : ℕ), 0 < m ∧
          ∃ (σ : MatrixRepresentation G (Fin m))
            (φ : ConjugationLinearMap (affineRegularRepresentation G V b hV) σ) (a : k),
            a ≠ 0 ∧ MatrixLinear.eval φ.coeff (RingHom.id k) w =
              a • (1 : Matrix (Fin m) (Fin m) k))
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (v : n → k) (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    ∃ (m : ℕ), 0 < m ∧
      ∃ (σ : MatrixRepresentation G (Fin m)) (φ : ConjugationLinearMap ρ σ) (a : k),
        a ≠ 0 ∧ MatrixLinear.eval φ.coeff (RingHom.id k) v =
          a • (1 : Matrix (Fin m) (Fin m) k) := by
  obtain ⟨V, d, b, hV, C, hC, h1⟩ :=
    exists_affine_finite_regular_map_to_one ρ v hv0 hv
  obtain ⟨m, hm, σ, φ, a, ha, hφ⟩ :=
    hregular V d b hV (C *ᵥ v) (hC.isFixedVector hv) h1
  refine ⟨m, hm, σ, φ.precomp hC, a, ha, ?_⟩
  change MatrixLinear.eval (MatrixLinear.precomp φ.coeff C) (RingHom.id k) v = _
  rw [MatrixLinear.eval_precomp]
  exact hφ

end Chevalley

end Langlands.GroupScheme
