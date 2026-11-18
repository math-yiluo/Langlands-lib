import Langlands.GroupScheme.Rational.PositivePowerFactorizationData
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.Representation.Plancherel.RationalMatrixNormComparison

/-! # Polynomial growth of real additive factors -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RealAdditiveFactor

/-- Pulling back a global function of the real additive group along a real point evaluates the
corresponding polynomial at the coordinate of the point. -/
theorem ΓSpecIso_appTop_vectorGroup
    (x : Over.mk (𝟙 (Spec (CommRingCat.of ℝ))) ⟶
      (VectorGroup.groupScheme (CommRingCat.of ℝ) 1).X)
    (P : VectorGroup.coordinateAlgebra (CommRingCat.of ℝ) 1) :
    (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom
        (x.left.appTop ((Scheme.ΓSpecIso
          (CommRingCat.of (VectorGroup.coordinateAlgebra (CommRingCat.of ℝ) 1))).inv P)) =
      eval (fun i => (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom
        ((VectorGroup.coordinates (CommRingCat.of ℝ) 1 _ x).toAdd i)) P := by
  erw [← Corepresented.adjunction_homEquiv_symm_apply x P]
  set ψ := (((algΓAlgSpecAdjunction (CommRingCat.of ℝ)).homEquiv _ _).symm x).unop.hom
  have hψ : ∀ i, ψ (X i) = (VectorGroup.coordinates (CommRingCat.of ℝ) 1 _ x).toAdd i := by
    intro i
    rw [VectorGroup.coordinates_apply]
    erw [Corepresented.adjunction_homEquiv_symm_apply]
  rw [MvPolynomial.aeval_unique ψ]
  let θ : ((algΓ (CommRingCat.of ℝ)).obj (Over.mk (𝟙 (Spec (CommRingCat.of ℝ))))).unop →+* ℝ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom.hom
  change θ (aeval (ψ ∘ X) P) = _
  rw [map_aeval]
  have hid : θ.comp (algebraMap (CommRingCat.of ℝ) _) = RingHom.id ℝ := Subsingleton.elim _ _
  rw [hid]
  simp only [Function.comp_apply, hψ]
  rfl


/-- The coordinate of the `N`-th power of the coordinate-one point is `N`. -/
theorem ΓSpecIso_coordinates_pow (N : ℕ) (i : Fin 1) :
    (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom
      ((VectorGroup.coordinates (CommRingCat.of ℝ) 1 _
        (VectorGroup.coordinateOnePoint ℝ ^ N)).toAdd i) = N := by
  rw [map_pow, MulEquiv.apply_symm_apply, toAdd_pow, toAdd_ofAdd, Pi.smul_apply, map_nsmul,
    map_one, nsmul_eq_mul, mul_one]

/-- The matrix entries of the image of the additive group grow at most polynomially along the
integer points. -/
theorem exists_rationalMatrix_entry_bound {G : GroupScheme (Spec (CommRingCat.of ℝ))}
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    (φ : VectorGroup.groupScheme (CommRingCat.of ℝ) 1 ⟶ G) (i j : n) :
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ N : ℕ,
      |(ρ.rationalMatrix (rationalPoints.map φ (VectorGroup.coordinateOnePoint ℝ ^ N)) :
        Matrix n n ℝ) i j| ≤ c * ((N : ℝ) + 1) ^ d := by
  set f := (φ.hom.hom ≫ ρ.hom.hom).left.appTop
    (GeneralLinear.entrySection n (CommRingCat.of ℝ) i j)
  set P := (Scheme.ΓSpecIso
    (CommRingCat.of (VectorGroup.coordinateAlgebra (CommRingCat.of ℝ) 1))).hom f
  obtain ⟨d, c, hc, hb⟩ := Langlands.Plancherel.polynomial_evaluation_power_bound
    (F := ℝ) (P : MvPolynomial (Fin 1) ℝ)
  refine ⟨d, c, hc, fun N => ?_⟩
  have hentry : (ρ.rationalMatrix (rationalPoints.map φ (VectorGroup.coordinateOnePoint ℝ ^ N)) :
      Matrix n n ℝ) i j = eval (fun _ => (N : ℝ)) P := by
    rw [MatrixRepresentation.rationalMatrix_apply_apply, rationalPoints.map_apply]
    have hf : f = (Scheme.ΓSpecIso
        (CommRingCat.of (VectorGroup.coordinateAlgebra (CommRingCat.of ℝ) 1))).inv P := by
      exact (Iso.hom_inv_id_apply _ f).symm
    have hcomp : ((VectorGroup.coordinateOnePoint ℝ ^ N) ≫ φ.hom.hom ≫ ρ.hom.hom).left.appTop
        (GeneralLinear.entrySection n (CommRingCat.of ℝ) i j) =
          (VectorGroup.coordinateOnePoint ℝ ^ N).left.appTop f := by
      simp only [f, Over.comp_left, Scheme.Hom.comp_appTop]
      rfl
    rw [Category.assoc, hcomp, hf, ΓSpecIso_appTop_vectorGroup]
    exact congrArg (fun v => eval v P) (funext fun i => ΓSpecIso_coordinates_pow N i)
  rw [hentry, ← coe_aeval_eq_eval]
  have := hb (fun _ => (N : ℝ)) ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])
    (fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg N.cast_nonneg]; linarith)
  rwa [Real.norm_eq_abs] at this

end Langlands.GroupScheme.RealAdditiveFactor
