import Langlands.CommutativeAlgebra.InvariantPolynomialCertificate
import Langlands.GroupScheme.Reductive.CovariantCoefficientFamily
import Langlands.GroupScheme.Reductive.InvariantPolynomialUniversal

/-! # Unit ideals in actual right-invariant section rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.InvariantPowerLift

set_option backward.isDefEq.respectTransparency false

open MvPolynomial
open Langlands.CommutativeAlgebra.InvariantPolynomialCertificate

section Polynomial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
  {I n : Type} [Fintype I] [Fintype n]

omit [Fintype n] in
/-- Express the family substitution using its scalar-extended polynomial. -/
theorem linearFamilyPolynomial_eq_eval_map (f : I → n → A) (F : MvPolynomial n k) :
    linearFamilyPolynomial f F =
      eval₂ C (fun j => ∑ i, X i * C (f i j)) (map (algebraMap k A) F) := by
  rw [eval₂_map]
  rfl

/-- Transforming every row is substitution in the original polynomial. -/
theorem linearFamilyPolynomial_matrix (M : Matrix n n A)
    (f : I → n → A) (F : MvPolynomial n k) :
    linearFamilyPolynomial (fun i => M *ᵥ f i) F =
      eval₂ C (fun j => ∑ i, X i * C (f i j))
        (MatrixRepresentation.linearPullback M (map (algebraMap k A) F)) := by
  rw [linearFamilyPolynomial_eq_eval_map, MatrixRepresentation.eval₂_linearPullback]
  congr 1
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Polynomial

variable {k : Type u} [Field k]
  {J H : GroupScheme (Spec (CommRingCat.of k))}
  {I n : Type} [Fintype I] [Fintype n] [DecidableEq n]

/-- The coefficients of a transpose-invariant polynomial in covariant rows
are invariant on every relative scheme test. -/
theorem isRightInvariant_coeff_linearFamilyPolynomial [IsAffine H.X.left]
    (iH : H ⟶ J) (ρ : MatrixRepresentation H n)
    (f : I → n → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hf : ∀ i, IsRightCovariantFamily iH ρ (f i))
    (F : MvPolynomial n k)
    (hF : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (x : n → Γ(T.left, ⊤)),
      eval₂ (scalarMap T) ((ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ x) F =
        eval₂ (scalarMap T) x F)
    (d : I →₀ ℕ) :
    HomogeneousQuotientFromEmbedding.IsRightInvariant iH
      ((linearFamilyPolynomial f F).coeff d) := by
  have hdual : ρ.dual.IsInvariantPolynomial F := by
    intro T h x
    simpa only [MatrixRepresentation.dual_pointMatrix,
      GeneralLinear.matrixContragredient_coe, map_inv] using hF T h⁻¹ x
  intro T g h
  let φ (a : T ⟶ J.X) :
      ((algΓ (CommRingCat.of k)).obj J.X).unop →ₐ[k]
        ((algΓ (CommRingCat.of k)).obj T).unop :=
    ((algΓ (CommRingCat.of k)).map a).unop.hom
  have hmatrix := hdual.actionPolynomial_of_isAffine h⁻¹
  rw [MatrixRepresentation.actionPolynomial, MatrixRepresentation.dual_pointMatrix,
    GeneralLinear.matrixContragredient_coe, map_inv, inv_inv] at hmatrix
  change MatrixRepresentation.linearPullback
      (show Matrix n n ((algΓ (CommRingCat.of k)).obj T).unop from
        (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ)
      (map (algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop) F) =
    map (algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop) F at hmatrix
  have hrows :
      (fun i j => φ (g * (h ≫ iH.hom.hom)) (f i j)) =
        (fun i => (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ
          (fun j => φ g (f i j))) := by
    funext i
    exact hf i T g h
  have he : map (φ (g * (h ≫ iH.hom.hom))).toRingHom (linearFamilyPolynomial f F) =
      map (φ g).toRingHom (linearFamilyPolynomial f F) := by
    rw [map_linearFamilyPolynomial, map_linearFamilyPolynomial, hrows,
      linearFamilyPolynomial_matrix, hmatrix, ← linearFamilyPolynomial_eq_eval_map]
  exact congrArg (fun P => P.coeff d) he

/-- The polynomial of covariant rows, with coefficients in the actual
right-invariant section ring. -/
def rightInvariantFamilyPolynomial [IsAffine H.X.left]
    (iH : H ⟶ J) (ρ : MatrixRepresentation H n)
    (f : I → n → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hf : ∀ i, IsRightCovariantFamily iH ρ (f i))
    (F : MvPolynomial n k)
    (hF : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (x : n → Γ(T.left, ⊤)),
      eval₂ (scalarMap T) ((ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ x) F =
        eval₂ (scalarMap T) x F) :
    MvPolynomial I (HomogeneousQuotientFromEmbedding.rightInvariantSubring iH) :=
  Classical.choose (exists_map_subring
    (HomogeneousQuotientFromEmbedding.rightInvariantSubring iH)
    (show MvPolynomial I Γ(J.X.left, ⊤) from
      linearFamilyPolynomial (A := ((algΓ (CommRingCat.of k)).obj J.X).unop) f F)
    (fun d => isRightInvariant_coeff_linearFamilyPolynomial iH ρ f hf F hF d))

/-- Including the invariant coefficients recovers the original row polynomial. -/
theorem map_rightInvariantFamilyPolynomial [IsAffine H.X.left]
    (iH : H ⟶ J) (ρ : MatrixRepresentation H n)
    (f : I → n → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hf : ∀ i, IsRightCovariantFamily iH ρ (f i))
    (F : MvPolynomial n k)
    (hF : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (x : n → Γ(T.left, ⊤)),
      eval₂ (scalarMap T) ((ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ x) F =
        eval₂ (scalarMap T) x F) :
    map (HomogeneousQuotientFromEmbedding.rightInvariantSubring iH).subtype
      (rightInvariantFamilyPolynomial iH ρ f hf F hF) =
        (show MvPolynomial I Γ(J.X.left, ⊤) from
          linearFamilyPolynomial (A := ((algΓ (CommRingCat.of k)).obj J.X).unop) f F) :=
  Classical.choose_spec (exists_map_subring
    (HomogeneousQuotientFromEmbedding.rightInvariantSubring iH)
    (show MvPolynomial I Γ(J.X.left, ⊤) from
      linearFamilyPolynomial (A := ((algΓ (CommRingCat.of k)).obj J.X).unop) f F)
    (fun d => isRightInvariant_coeff_linearFamilyPolynomial iH ρ f hf F hF d))

omit [Fintype n] [DecidableEq n] in
/-- An ambient unit-ideal relation among actual invariant functions already
generates the unit ideal in the invariant subring, assuming geometric reductivity. -/
theorem span_eq_top_rightInvariantSubring
    [IsAlgClosed k] [Smooth H.X.hom] [IsAffine J.X.left] [IsAffine H.X.left]
    (iH : H ⟶ J) (hH : IsGeometricallyReductive H)
    (s : I → HomogeneousQuotientFromEmbedding.rightInvariantSubring iH)
    (a : I → Γ(J.X.left, ⊤))
    (ha : ∑ i, (s i : Γ(J.X.left, ⊤)) * a i = 1) :
    Ideal.span (Set.range s) = ⊤ := by
  classical
  let : Algebra k Γ(J.X.left, ⊤) :=
    inferInstanceAs (Algebra k ((algΓ (CommRingCat.of k)).obj J.X).unop)
  obtain ⟨d, ρ, g, c, hg, hc, hc0, hfix⟩ :=
    exists_scalar_covariant_coefficients iH (fun i => (s i : Γ(J.X.left, ⊤)))
      (fun i => (s i).property) a ha
  obtain ⟨e, F, he, hF, hFinv, hFc⟩ :=
    MatrixRepresentation.exists_normalized_transpose_invariant hH ρ c hc0 hfix
  let g' : I → Fin d → Γ(J.X.left, ⊤) := g
  apply span_eq_top_of_polynomial_certificate
    (HomogeneousQuotientFromEmbedding.rightInvariantSubring iH) s
    (linearFamilyPolynomial g' F)
  · intro m
    exact isRightInvariant_coeff_linearFamilyPolynomial iH ρ g hg F hFinv m
  · rw [constantCoeff_linearFamilyPolynomial]
    have hzero : constantCoeff F = 0 := by
      change F.coeff 0 = 0
      exact hF.coeff_eq_zero (by simpa [Finsupp.degree] using he.ne)
    rw [hzero, map_zero]
  · rw [eval_linearFamilyPolynomial]
    have hweighted :
        (fun j => ∑ i, (s i : Γ(J.X.left, ⊤)) * g' i j) =
          (fun j => algebraMap k Γ(J.X.left, ⊤) (c j)) := by
      funext j
      exact hc j
    rw [hweighted]
    simpa only [mul_one, one_pow] using aeval_scaled_eq_pow hF c hFc (1 : Γ(J.X.left, ⊤))

end Langlands.GroupScheme.InvariantPowerLift
