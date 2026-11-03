import Langlands.Global.RepresentationHeightDominationStatement

/-! # Polynomial comparison with a closed algebraic embedding height: proof -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial NumberField
open scoped Classical Matrix.Norms.Operator CategoryTheory.MonObj

namespace Langlands.Global.RepresentationGrowth

section Coordinates

open GroupScheme GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the regular function of a polynomial at an affine point of the general
linear group evaluates the polynomial at the point's matrix and inverse entries. -/
theorem affinePointEvaluation_quotient {S : CommAlgCat.{u} R}
    (y : (groupScheme n R).affinePoints S) (p : MvPolynomial (Coordinate n) R) :
    (groupScheme n R).affinePointEvaluation S y
        ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).inv (quotient n R p)) =
      aeval (values (affinePointsEquiv n R S y)) p := by
  conv_lhs => rw [← (affinePointsEquiv n R S).symm_apply_apply y]
  rw [affinePointsEquiv_symm_apply, affinePointEvaluation_map_classify, Iso.inv_hom_id_apply,
    classify_quotient]

/-- Through a closed matrix embedding `rho`, every matrix or inverse-matrix coordinate of
an arbitrary matrix representation `sigma` is a fixed polynomial in the matrix and
inverse-matrix coordinates of `rho`, at all affine points. -/
theorem exists_coordinate_polynomial {G : GroupScheme (Spec R)} {m : Type} [Fintype m]
    [DecidableEq m] (rho : MatrixRepresentation G n) (sigma : MatrixRepresentation G m)
    (hrho : IsClosedSubgroup rho) (c : Coordinate m) :
    ∃ p : MvPolynomial (Coordinate n) R, ∀ (S : CommAlgCat.{u} R) (x : G.affinePoints S),
      values (affinePointsEquiv m R S (x ≫ sigma.hom.hom)) c =
        aeval (values (affinePointsEquiv n R S (x ≫ rho.hom.hom))) p := by
  have : IsClosedImmersion rho.hom.hom.left := hrho
  obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine rho.hom.hom.left
  obtain ⟨t, ht⟩ := hsurj (sigma.hom.hom.left.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing m R))).inv (quotient m R (X c))))
  obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective R (ideal n R)
    ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).hom t)
  refine ⟨p, fun S x => ?_⟩
  have ht' : (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).inv (quotient n R p) = t := by
    rw [hp]
    exact Iso.hom_inv_id_apply _ t
  calc
    values (affinePointsEquiv m R S (x ≫ sigma.hom.hom)) c =
        (groupScheme m R).affinePointEvaluation S (x ≫ sigma.hom.hom)
          ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing m R))).inv (quotient m R (X c))) := by
      rw [affinePointEvaluation_quotient, aeval_X]
    _ = G.affinePointEvaluation S x (rho.hom.hom.left.appTop t) := by
      rw [ht]
      rfl
    _ = (groupScheme n R).affinePointEvaluation S (x ≫ rho.hom.hom) t := rfl
    _ = aeval (values (affinePointsEquiv n R S (x ≫ rho.hom.hom))) p := by
      rw [← ht', affinePointEvaluation_quotient]

end Coordinates

section Bounds

variable {X : Type*} (h : X → ℝ)

/-- A real function bounded by a constant multiple of a natural power of `h`. -/
def PolyBounded (f : X → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x, f x ≤ C * h x ^ d

variable {h}

theorem PolyBounded.mono {f g : X → ℝ} (hg : PolyBounded h g) (hfg : ∀ x, f x ≤ g x) :
    PolyBounded h f := by
  obtain ⟨C, hC, d, hg⟩ := hg
  exact ⟨C, hC, d, fun x => (hfg x).trans (hg x)⟩

theorem polyBounded_const (c : ℝ) : PolyBounded h (fun _ => c) :=
  ⟨max c 0, le_max_right _ _, 0, fun _ => by simp⟩

theorem PolyBounded.add (h1 : ∀ x, 1 ≤ h x) {f g : X → ℝ} (hf : PolyBounded h f)
    (hg : PolyBounded h g) : PolyBounded h (fun x => f x + g x) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, max d e, fun x => ?_⟩
  calc
    f x + g x ≤ C * h x ^ d + D * h x ^ e := add_le_add (hf x) (hg x)
    _ ≤ C * h x ^ max d e + D * h x ^ max d e :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1 x) (le_max_left d e)) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1 x) (le_max_right d e)) hD)
    _ = (C + D) * h x ^ max d e := (add_mul _ _ _).symm

theorem polyBounded_sum (h1 : ∀ x, 1 ≤ h x) {κ : Type*} (s : Finset κ) {f : κ → X → ℝ}
    (hf : ∀ i ∈ s, PolyBounded h (f i)) : PolyBounded h (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyBounded_const (h := h) 0
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add h1
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem PolyBounded.mul_le {f g : X → ℝ} (hf : PolyBounded h f) (hf0 : ∀ x, 0 ≤ f x)
    (hg : ∀ x, g x ≤ h x) (hg0 : ∀ x, 0 ≤ g x) : PolyBounded h (fun x => f x * g x) := by
  obtain ⟨C, hC, d, hf'⟩ := hf
  refine ⟨C, hC, d + 1, fun x => ?_⟩
  calc
    f x * g x ≤ (C * h x ^ d) * h x :=
      mul_le_mul (hf' x) (hg x) (hg0 x) ((hf0 x).trans (hf' x))
    _ = C * h x ^ (d + 1) := by rw [pow_succ]; ring

/-- A fixed polynomial, evaluated at variables whose images have norm at most `h`, is
bounded by a constant multiple of a natural power of `h`. -/
theorem polyBounded_aeval {σ K A B : Type*} [CommRing K] [CommRing A] [Algebra K A]
    [NormedRing B] (φ : A →+* B) (v : X → σ → A) (h1 : ∀ x, 1 ≤ h x)
    (hv : ∀ x i, ‖φ (v x i)‖ ≤ h x) (p : MvPolynomial σ K) :
    PolyBounded h (fun x => ‖φ (aeval (v x) p)‖) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [aeval_C] using polyBounded_const (h := h) ‖φ (algebraMap K A r)‖
  | add p q hp hq =>
      refine (hp.add h1 hq).mono fun x => ?_
      rw [map_add, map_add]
      exact norm_add_le _ _
  | mul_X p i hp =>
      refine (hp.mul_le (fun x => norm_nonneg _) (fun x => hv x i)
        (fun x => norm_nonneg _)).mono fun x => ?_
      rw [map_mul, aeval_X, map_mul]
      exact norm_mul_le _ _

end Bounds

section MatrixNorm

variable {m α : Type*} [Fintype m] [SeminormedAddCommGroup α]

/-- An entry is bounded by the row-sum operator norm. -/
theorem norm_entry_le_linfty_opNorm (A : Matrix m m α) (i j : m) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 : ∑ k, ‖A i k‖₊ ≤ Finset.univ.sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

/-- The row-sum operator norm is bounded by the sum of all entry norms. -/
theorem linfty_opNorm_le_sum (A : Matrix m m α) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ ∑ i, ∑ j, ‖A i j‖₊ :=
    Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖₊) (fun _ _ => zero_le)
        (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_sum, coe_nnnorm] using h'

end MatrixNorm

open GroupScheme.GeneralLinear in
/-- A closed matrix embedding polynomially dominates the height of every matrix
representation on the actual infinite adelic points. -/
theorem closedImmersionHeightDomination : ClosedImmersionHeightDominationStatement.{u} := by
  intro F _ _ G N M rho sigma hrho
  choose p hp using exists_coordinate_polynomial rho sigma hrho
  let φ : InfiniteAdeleRing F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
  have h1 : ∀ g, 1 ≤ height F G rho g := one_le_height F G rho
  have hmat : ∀ {n : ℕ} (G' : GroupScheme (Spec (CommRingCat.of F)))
      (tau : GroupScheme.MatrixRepresentation G' (Fin n)) (g : InfiniteAdelicGroupPoints F G'),
      infiniteMatrix F G' tau g = affinePointsEquiv (Fin n) (CommRingCat.of F)
        (CommAlgCat.of F (InfiniteAdeleRing F)) (g ≫ tau.hom.hom) := fun _ _ _ => rfl
  have hentry : ∀ {n : ℕ} (a : InfiniteAdelicGL F n) (i j : Fin n),
      φ (values a (Coordinate.entry i j)) = (archimedeanGLCoordinates F n a).val i j :=
    fun _ _ _ => rfl
  have hinv : ∀ {n : ℕ} (a : InfiniteAdelicGL F n) (i j : Fin n),
      φ (values a (Coordinate.inverseEntry i j)) = (archimedeanGLCoordinates F n a).inv i j :=
    fun _ _ _ => rfl
  have hv : ∀ g c, ‖φ (values (infiniteMatrix F G rho g) c)‖ ≤ height F G rho g := by
    intro g c
    cases c with
    | entry i j =>
        rw [hentry]
        exact (norm_entry_le_linfty_opNorm _ i j).trans
          (ArchimedeanGL.norm_val_le_matrixHeight F N _)
    | inverseEntry i j =>
        rw [hinv]
        exact (norm_entry_le_linfty_opNorm _ i j).trans
          (ArchimedeanGL.norm_inv_le_matrixHeight F N _)
  have hc : ∀ c, PolyBounded (height F G rho)
      (fun g => ‖φ (values (infiniteMatrix F G sigma g) c)‖) := by
    intro c
    refine (polyBounded_aeval φ (fun g => values (infiniteMatrix F G rho g)) h1 hv
      (p c)).mono fun g => le_of_eq ?_
    rw [hmat, hmat, hp c]
  have hval : PolyBounded (height F G rho)
      (fun g => ‖(archimedeanGLCoordinates F M (infiniteMatrix F G sigma g)).val‖) :=
    (polyBounded_sum h1 Finset.univ fun i _ => polyBounded_sum h1 Finset.univ fun j _ =>
      hc (Coordinate.entry i j)).mono fun g => by
        refine (linfty_opNorm_le_sum _).trans (le_of_eq ?_)
        simp only [← hentry]
  have hinvb : PolyBounded (height F G rho)
      (fun g => ‖(archimedeanGLCoordinates F M (infiniteMatrix F G sigma g)).inv‖) :=
    (polyBounded_sum h1 Finset.univ fun i _ => polyBounded_sum h1 Finset.univ fun j _ =>
      hc (Coordinate.inverseEntry i j)).mono fun g => by
        refine (linfty_opNorm_le_sum _).trans (le_of_eq ?_)
        simp only [← hinv]
  have hheight : PolyBounded (height F G rho) (height F G sigma) := by
    refine (((polyBounded_const 1).add h1 hval).add h1 hinvb).mono fun g => ?_
    have ha := norm_nonneg (archimedeanGLCoordinates F M (infiniteMatrix F G sigma g)).val
    have hb := norm_nonneg (archimedeanGLCoordinates F M (infiniteMatrix F G sigma g)).inv
    change max 1 (max _ _) ≤ _
    refine max_le (by linarith) (max_le (by linarith) (by linarith))
  obtain ⟨C, -, d, hb⟩ := hheight
  refine ⟨max C 1, le_max_right _ _, d, fun g => (hb g).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (height_nonneg F G rho g) d)

end Langlands.Global.RepresentationGrowth
