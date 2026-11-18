import Langlands.GroupScheme.Rational.InvariantCoordinateIntegral
import Langlands.GroupScheme.Reductive.InvariantPolynomialUniversal

/-! # Averaging polynomial functions using an invariant coordinate integral -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.PolynomialAverage

open CoordinateIntegration

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- The action on vectors over an arbitrary coefficient algebra. -/
abbrev action (A : Type u) [CommRing A] [Algebra k A] :=
  ρ.affineAction (CommAlgCat.of (CommRingCat.of k) A)

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

omit [IsAffineHom G.X.hom] in
theorem map_action (f : A →ₐ[k] B) (t : Lie.AffinePoints G A) (x : n → A) :
    (fun i => f (action ρ A t x i)) =
      action ρ B (Lie.affineMap G f t) (fun i => f (x i)) := by
  exact (ρ.affineAction_naturality (CommAlgCat.ofHom f) t x).symm

/-- Evaluate a polynomial on the inverse universal translate of a vector. -/
def orbit (x : n → A) : MvPolynomial n k →ₐ[k] A ⊗[k] Coord G :=
  MvPolynomial.aeval (action ρ (A ⊗[k] Coord G) (universalPoint G A)⁻¹
    (fun i => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) (x i)))

theorem orbit_naturality (f : A →ₐ[k] B) (x : n → A) (F : MvPolynomial n k) :
    tensorMap G f (orbit ρ x F) = orbit ρ (fun i => f (x i)) F := by
  have h : (tensorMap G f).comp (orbit ρ x) = orbit ρ (fun i => f (x i)) := by
    ext i
    simp only [AlgHom.comp_apply, orbit, MvPolynomial.aeval_X]
    have hm := map_action ρ (tensorMap G f) (universalPoint G A)⁻¹
      (fun j => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) (x j))
    rw [map_inv (Lie.affineMap G (tensorMap G f)), tensorMap_universalPoint] at hm
    rw [congrFun hm i]
    congr 2
  exact AlgHom.congr_fun h F

/-- Translating the integration variable is inverse translation of the input vector. -/
theorem orbit_leftTranslation (t : Lie.AffinePoints G A) (x : n → A)
    (F : MvPolynomial n k) :
    leftTranslation G A t (orbit ρ x F) = orbit ρ (action ρ A t⁻¹ x) F := by
  have h : ((leftTranslation G A t).restrictScalars k).comp (orbit ρ x) =
      orbit ρ (action ρ A t⁻¹ x) := by
    ext i
    simp only [AlgHom.comp_apply, orbit, MvPolynomial.aeval_X]
    have hm := map_action ρ ((leftTranslation G A t).restrictScalars k)
      (universalPoint G A)⁻¹ (fun j => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) (x j))
    rw [map_inv (Lie.affineMap G ((leftTranslation G A t).restrictScalars k)),
      leftTranslation_universalPoint, mul_inv_rev, map_mul,
      LinearEquiv.mul_apply] at hm
    have hv : (fun j => ((leftTranslation G A t).restrictScalars k)
        ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) (x j))) =
        (fun j => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) (x j)) := by
      funext j
      exact AlgHom.congr_fun (leftTranslation_includeLeft G t) (x j)
    rw [hv] at hm
    rw [congrFun hm i]
    apply congrArg (fun v : n → A ⊗[k] Coord G =>
      action ρ (A ⊗[k] Coord G) (universalPoint G A)⁻¹ v i)
    simpa only [map_inv] using (map_action ρ
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) t⁻¹ x).symm
  exact AlgHom.congr_fun h F

variable (I : InvariantIntegral G)

/-- Average the inverse universal translate of the generic vector. -/
def reynolds : MvPolynomial n k →ₗ[k] MvPolynomial n k :=
  (I.average (A := MvPolynomial n k)).restrictScalars k ∘ₗ
    (orbit ρ (MvPolynomial.X : n → MvPolynomial n k)).toLinearMap

theorem eval_reynolds (x : n → A) (F : MvPolynomial n k) :
    MvPolynomial.aeval x (reynolds ρ I F) = I.average (orbit ρ x F) := by
  rw [reynolds, LinearMap.comp_apply]
  change MvPolynomial.aeval x (contract G _ I.linearForm _) = _
  rw [← contract_naturality G I.linearForm (MvPolynomial.aeval x)]
  change contract G A I.linearForm (tensorMap G (MvPolynomial.aeval x)
    (orbit ρ MvPolynomial.X F)) = _
  rw [orbit_naturality]
  simp only [MvPolynomial.aeval_X]

theorem eval_reynolds_action (t : Lie.AffinePoints G A) (x : n → A)
    (F : MvPolynomial n k) :
    MvPolynomial.aeval (action ρ A t x) (reynolds ρ I F) =
      MvPolynomial.aeval x (reynolds ρ I F) := by
  rw [eval_reynolds, eval_reynolds]
  have h := orbit_leftTranslation ρ t⁻¹ x F
  rw [inv_inv] at h
  rw [← h]
  exact I.left_invariant A t⁻¹ _

/-- Invariance of affine evaluations implies invariance on every scheme test. -/
theorem invariant_of_affine_eval (F : MvPolynomial n k)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : Lie.AffinePoints G A) (x : n → A),
      MvPolynomial.aeval (action ρ A t x) F = MvPolynomial.aeval x F) :
    ρ.IsInvariantPolynomial F := by
  let C := Coord G
  let g : (algSpec (CommRingCat.of k)).obj (op C) ⟶ G.X :=
    (Lie.coordinateIso G).hom
  have h : linearPullback (ρ.affineMatrix C g : Matrix n n C)
      (MvPolynomial.map (algebraMap k C) F) =
        MvPolynomial.map (algebraMap k C) F := by
    let B := CommAlgCat.of (CommRingCat.of k) (MvPolynomial n C)
    let f : C ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k C (MvPolynomial n C))
    have h := hF B ((algSpec (CommRingCat.of k)).map f.op ≫ g) MvPolynomial.X
    change MvPolynomial.eval₂ (algebraMap k B)
      ((ρ.affineMatrix B _ : Matrix n n B) *ᵥ MvPolynomial.X) F = _ at h
    rw [affineMatrix_naturality] at h
    have hs : algebraMap k B = (MvPolynomial.C : C →+* MvPolynomial n C).comp
        (algebraMap k C) := by
      apply RingHom.ext
      intro c
      exact IsScalarTower.algebraMap_apply k C (MvPolynomial n C) c
    rw [hs] at h
    rw [linearPullback, MvPolynomial.eval₂_map,
      MvPolynomial.map_eq_eval₂Hom_C_comp]
    exact h
  have : Epi (Lie.coordinateIso G).hom.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_epi (Lie.coordinateIso G).hom
  apply ρ.isInvariantPolynomial_of_epi_polynomial (Lie.coordinateIso G).hom F
  let q : C →+* Γ(((algSpec (CommRingCat.of k)).obj (op C)).left, ⊤) :=
    (Corepresented.affineSectionsIso C).inv.hom.toRingHom
  have hs : q.comp (algebraMap k C) =
      scalarMap ((algSpec (CommRingCat.of k)).obj (op C)) := by
    ext c
    exact (UnipotentMatrixCriterion.scalarMap_affine C c).symm
  have h₀ := congrArg (MvPolynomial.map q) h
  rw [map_linearPullback, MvPolynomial.map_map, hs] at h₀
  rw [actionPolynomial, pointMatrix_eq_affineMatrix]
  exact h₀

/-- Averaging lands in the polynomials invariant on every scheme test. -/
theorem reynolds_invariant (F : MvPolynomial n k) :
    ρ.IsInvariantPolynomial (reynolds ρ I F) := by
  apply invariant_of_affine_eval ρ
  intro A _ _ t x
  exact eval_reynolds_action ρ I t x F

/-- An invariant polynomial is constant along the inverse universal orbit. -/
theorem orbit_invariant {F : MvPolynomial n k} (hF : ρ.IsInvariantPolynomial F)
    (x : n → A) : orbit ρ x F =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G)
        (MvPolynomial.aeval x F) := by
  calc
    orbit ρ x F = MvPolynomial.aeval
        (fun i => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) (x i)) F :=
      hF.affine (CommAlgCat.of (CommRingCat.of k) (A ⊗[k] Coord G))
        (universalPoint G A)⁻¹ _
    _ = _ := (MvPolynomial.comp_aeval_apply x
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) F).symm

/-- Normalization makes averaging the identity on invariant polynomials. -/
theorem reynolds_eq_self {F : MvPolynomial n k} (hF : ρ.IsInvariantPolynomial F) :
    reynolds ρ I F = F := by
  change I.average (orbit ρ MvPolynomial.X F) = F
  rw [orbit_invariant ρ hF, InvariantIntegral.average_includeLeft]
  exact MvPolynomial.aeval_X_left_apply F

/-- Averaging commutes with multiplication by an invariant polynomial. -/
theorem reynolds_mul {s : MvPolynomial n k} (hs : ρ.IsInvariantPolynomial s)
    (F : MvPolynomial n k) :
    reynolds ρ I (s * F) = s * reynolds ρ I F := by
  change I.average (orbit ρ MvPolynomial.X (s * F)) = _
  rw [map_mul, orbit_invariant ρ hs, MvPolynomial.aeval_X_left_apply]
  have hleft : (Algebra.TensorProduct.includeLeft : MvPolynomial n k →ₐ[k]
      MvPolynomial n k ⊗[k] Coord G) s =
        algebraMap (MvPolynomial n k) (MvPolynomial n k ⊗[k] Coord G) s := by
    simp only [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hleft, ← Algebra.smul_def, map_smul]
  rfl

end Langlands.GroupScheme.MatrixRepresentation.PolynomialAverage
