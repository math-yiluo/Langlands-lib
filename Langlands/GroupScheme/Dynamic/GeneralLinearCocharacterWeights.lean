import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Torus.GmEndomorphismsProof
import Langlands.GroupScheme.AffinePoints
import Langlands.LinearAlgebra.OrthogonalIdempotentDiagonal
import Langlands.GroupScheme.InnerAutomorphism

/-! # Weight projectors of a cocharacter of `GL_n` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Gm

variable {R : CommRingCat.{u}} {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
  [Algebra R B]

/-- The unit coordinate of a point of `𝔾_m` over a test algebra. -/
abbrev algebraPointsEquiv (A : Type u) [CommRing A] [Algebra R A] :
    Lie.AffinePoints (Gm (Spec R)).toGrp A ≃* Aˣ :=
  affinePointsEquiv ((algSpec R).obj (op (CommAlgCat.of R A))).hom

/-- Unit coordinates of points of `𝔾_m` commute with change of test algebra. -/
theorem algebraPointsEquiv_naturality (f : A →ₐ[R] B)
    (t : Lie.AffinePoints (Gm (Spec R)).toGrp A) :
    algebraPointsEquiv B (Lie.affineMap _ f t) =
      Units.map f.toMonoidHom (algebraPointsEquiv A t) := by
  change affinePointsEquiv _ ((algSpec R).map (CommAlgCat.ofHom f).op ≫ t) = _
  apply Units.ext
  rw [affinePointsEquiv_val, pointsEquiv_naturality]
  change ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom) _ =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

theorem algebraPointsEquiv_symm_naturality (f : A →ₐ[R] B) (u : Aˣ) :
    (algebraPointsEquiv B).symm (Units.map f.toMonoidHom u) =
      Lie.affineMap _ f ((algebraPointsEquiv A).symm u) := by
  apply (algebraPointsEquiv B).injective
  rw [MulEquiv.apply_symm_apply, algebraPointsEquiv_naturality, MulEquiv.apply_symm_apply]

end Gm

namespace GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R : CommRingCat.{u}}
  (χ : (Gm (Spec R)).toGrp ⟶ groupScheme n R)

/-- The matrices `χ(u)` of a cocharacter `χ` of `GL_n` at the units `u` of a test algebra. -/
def cocharacterUnitsHom (A : Type u) [CommRing A] [Algebra R A] : Aˣ →* GL n A where
  toFun u := affinePointsEquiv n R (CommAlgCat.of R A)
    ((Gm.algebraPointsEquiv A).symm u ≫ χ.hom.hom)
  map_one' := by
    rw [map_one, MonObj.one_comp, map_one]
  map_mul' u v := by
    rw [map_mul, MonObj.mul_comp, map_mul]

variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The matrices of a cocharacter commute with change of test algebra. -/
theorem cocharacterUnitsHom_naturality (f : A →ₐ[R] B) (u : Aˣ) :
    cocharacterUnitsHom χ B (Units.map f.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.toRingHom (cocharacterUnitsHom χ A u) := by
  change affinePointsEquiv n R (CommAlgCat.of R B)
      ((Gm.algebraPointsEquiv B).symm (Units.map f.toMonoidHom u) ≫ χ.hom.hom) = _
  rw [Gm.algebraPointsEquiv_symm_naturality, Lie.affineMap_apply, Category.assoc,
    affinePointsEquiv_naturality]
  rfl

/-! ### Weight projectors -/

section Projectors

variable (R) in
/-- The Laurent coordinate `T` as a unit of `R[T, T⁻¹]`. -/
def cocharacterLaurentUnit : (LaurentPolynomial R)ˣ := (LaurentPolynomial.isUnit_T 1).unit

omit [Fintype n] [DecidableEq n] in
@[simp] theorem cocharacterLaurentUnit_val :
    ((cocharacterLaurentUnit R : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T 1 :=
  rfl

/-- The matrix `χ(T)` of a cocharacter at the Laurent coordinate. -/
def weightMatrix : GL n (LaurentPolynomial R) :=
  cocharacterUnitsHom χ (LaurentPolynomial R) (cocharacterLaurentUnit R)

/-- The weight projector `E_a` of a cocharacter `χ`: the matrix of `T ^ a`-coefficients of
`χ(T)`. -/
def weightProjector (a : ℤ) : Matrix n n R :=
  Matrix.of fun i j => ((weightMatrix χ : Matrix n n (LaurentPolynomial R)) i j).coeff a

theorem weightProjector_apply (a : ℤ) (i j : n) :
    weightProjector χ a i j =
      ((weightMatrix χ : Matrix n n (LaurentPolynomial R)) i j).coeff a :=
  rfl

/-- The finite set of weights occurring in `χ(T)`. -/
def cocharacterWeightSupport : Finset ℤ :=
  Finset.univ.biUnion fun p : n × n =>
    ((weightMatrix χ : Matrix n n (LaurentPolynomial R)) p.1 p.2).coeff.support

theorem weightProjector_eq_zero {a : ℤ} (ha : a ∉ cocharacterWeightSupport χ) :
    weightProjector χ a = 0 := by
  ext i j
  rw [weightProjector_apply, Matrix.zero_apply]
  by_contra h
  exact ha (Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)

/-- Each entry of `χ(T)` is the Laurent polynomial with coefficients the projector entries. -/
theorem weightMatrix_apply (i j : n) :
    (weightMatrix χ : Matrix n n (LaurentPolynomial R)) i j =
      ∑ a ∈ cocharacterWeightSupport χ, AddMonoidAlgebra.single a (weightProjector χ a i j) := by
  apply AddMonoidAlgebra.coeff_injective
  ext b
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hb
  · rfl
  · by_contra h
    exact hb (Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _,
      Finsupp.mem_support_iff.mpr h⟩)

/-! #### Completeness: evaluation at `T = 1` -/

variable (R) in
/-- Evaluation of Laurent polynomials at `T = 1`, as an algebra map. -/
def cocharacterEvalOne : LaurentPolynomial R →ₐ[R] R :=
  AddMonoidAlgebra.lift R R ℤ 1

omit [Fintype n] [DecidableEq n] in
@[simp] theorem cocharacterEvalOne_single (a : ℤ) (r : R) :
    cocharacterEvalOne R (AddMonoidAlgebra.single a r) = r := by
  rw [cocharacterEvalOne, AddMonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

omit [Fintype n] [DecidableEq n] in
theorem units_map_cocharacterEvalOne :
    Units.map (cocharacterEvalOne R).toMonoidHom (cocharacterLaurentUnit R) = 1 := by
  apply Units.ext
  change cocharacterEvalOne R (AddMonoidAlgebra.single 1 1) = 1
  rw [cocharacterEvalOne_single]

/-- The weight projectors sum to the identity matrix. -/
theorem sum_weightProjector : ∑ a ∈ cocharacterWeightSupport χ, weightProjector χ a = 1 := by
  have h := cocharacterUnitsHom_naturality χ (cocharacterEvalOne R) (cocharacterLaurentUnit R)
  rw [units_map_cocharacterEvalOne, map_one] at h
  ext i j
  have hij := congrArg (fun g : GL n R => (g : Matrix n n R) i j) h
  simp only [Units.val_one] at hij
  rw [hij, Matrix.sum_apply]
  change _ = cocharacterEvalOne R ((weightMatrix χ : Matrix n n (LaurentPolynomial R)) i j)
  rw [weightMatrix_apply, map_sum]
  simp only [cocharacterEvalOne_single]

/-! #### Orthogonality: translation `T ↦ s T` -/

variable (R) in
/-- The monomials `T ^ m` of `R[T, T⁻¹][S, S⁻¹]` with coefficient `T ^ m`: the values of the
translation `T ↦ T S`. -/
def cocharacterTranslateMonomial :
    Multiplicative ℤ →* AddMonoidAlgebra (LaurentPolynomial R) ℤ where
  toFun m := AddMonoidAlgebra.single m.toAdd (LaurentPolynomial.T m.toAdd)
  map_one' := by
    rw [toAdd_one, LaurentPolynomial.T_zero]
    rfl
  map_mul' a b := by
    rw [toAdd_mul, AddMonoidAlgebra.single_mul_single, LaurentPolynomial.T_add]

variable (R) in
/-- The translation `R[T, T⁻¹] → R[T, T⁻¹][S, S⁻¹]`, `T ↦ T S`. -/
def cocharacterTranslate : LaurentPolynomial R →ₐ[R] AddMonoidAlgebra (LaurentPolynomial R) ℤ :=
  AddMonoidAlgebra.lift R _ ℤ (cocharacterTranslateMonomial R)

omit [Fintype n] [DecidableEq n] in
theorem cocharacterTranslate_single (m : ℤ) (r : R) :
    cocharacterTranslate R (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single m (r • LaurentPolynomial.T m) := by
  rw [cocharacterTranslate, AddMonoidAlgebra.lift_single]
  change r • AddMonoidAlgebra.single m (LaurentPolynomial.T m) = _
  rw [AddMonoidAlgebra.smul_single]

omit [Fintype n] [DecidableEq n] in
theorem coeff_cocharacterTranslate (x : LaurentPolynomial R) (m : ℤ) :
    (cocharacterTranslate R x).coeff m = x.coeff m • LaurentPolynomial.T m := by
  classical
  have h (p : ℤ →₀ R) :
      (cocharacterTranslate R (AddMonoidAlgebra.ofCoeff p)).coeff m =
        p m • LaurentPolynomial.T m := by
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
        rw [AddMonoidAlgebra.ofCoeff_add, map_add, AddMonoidAlgebra.coeff_add,
          Finsupp.add_apply, hp, hq, Finsupp.add_apply, add_smul]
    | single k r =>
        change (cocharacterTranslate R (AddMonoidAlgebra.single k r)).coeff m = _
        rw [cocharacterTranslate_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
          Finsupp.single_apply]
        split_ifs with hk
        · subst hk
          rfl
        · rw [zero_smul]
  exact h x.coeff

omit [Fintype n] [DecidableEq n] in
theorem units_map_cocharacterTranslate :
    Units.map (cocharacterTranslate R).toMonoidHom (cocharacterLaurentUnit R) =
      Units.map (AddMonoidAlgebra.singleZeroAlgHom (R := R)).toMonoidHom
          (cocharacterLaurentUnit R) *
        Units.map (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R (LaurentPolynomial R))).toMonoidHom
          (cocharacterLaurentUnit R) := by
  apply Units.ext
  change cocharacterTranslate R (AddMonoidAlgebra.single 1 1) =
    AddMonoidAlgebra.single 0 (LaurentPolynomial.T 1) *
      AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R (LaurentPolynomial R))
        (AddMonoidAlgebra.single 1 1)
  rw [cocharacterTranslate_single, one_smul]
  apply AddMonoidAlgebra.coeff_injective
  ext b
  rw [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_mapAlgHom,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- The weight projectors are orthogonal idempotents. -/
theorem weightProjector_mul (p m : ℤ) :
    weightProjector χ p * weightProjector χ m =
      if p = m then weightProjector χ m else 0 := by
  have hτ := cocharacterUnitsHom_naturality χ (cocharacterTranslate R) (cocharacterLaurentUnit R)
  rw [units_map_cocharacterTranslate, map_mul, cocharacterUnitsHom_naturality,
    cocharacterUnitsHom_naturality] at hτ
  -- entrywise, at the coefficient `S ^ m`
  have key : ∀ i j, (weightProjector χ m i j) • LaurentPolynomial.T m =
      ∑ l, (weightMatrix χ : Matrix n n (LaurentPolynomial R)) i l *
        algebraMap R (LaurentPolynomial R) (weightProjector χ m l j) := by
    intro i j
    have h0 := congrArg (fun g : GL n (AddMonoidAlgebra (LaurentPolynomial R) ℤ) =>
      ((g : Matrix n n (AddMonoidAlgebra (LaurentPolynomial R) ℤ)) i j).coeff m) hτ
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_mul, Matrix.mul_apply] at h0
    have h : ((cocharacterTranslate R) ((weightMatrix χ : Matrix n n _) i j)).coeff m =
        (∑ l, AddMonoidAlgebra.single 0 ((weightMatrix χ : Matrix n n _) i l) *
          AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R (LaurentPolynomial R))
            ((weightMatrix χ : Matrix n n (LaurentPolynomial R)) l j)).coeff m :=
      h0.symm
    rw [coeff_cocharacterTranslate, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h
    rw [weightProjector_apply, h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_mapAlgHom]
    rfl
  ext i j
  have h := congrArg (fun x : LaurentPolynomial R => x.coeff p) (key i j)
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h
  rw [Matrix.mul_apply]
  have hr : ∀ l, ((weightMatrix χ : Matrix n n (LaurentPolynomial R)) i l *
      algebraMap R (LaurentPolynomial R) (weightProjector χ m l j)).coeff p =
        weightProjector χ p i l * weightProjector χ m l j := by
    intro l
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
      AddMonoidAlgebra.coeff_mul_single_zero]
    rfl
  simp only [hr] at h
  rw [← h]
  rw [LaurentPolynomial.T, AddMonoidAlgebra.smul_single', mul_one, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

end Projectors

/-! ### Comparison with diagonal cocharacters and base points -/

section Comparison

theorem cocharacterUnitsHom_apply (u : Aˣ) :
    cocharacterUnitsHom χ A u = affinePointsEquiv n R (CommAlgCat.of R A)
      ((Gm.algebraPointsEquiv A).symm u ≫ χ.hom.hom) :=
  rfl

/-- Affine coordinates are the global-section coordinates transported along `Γ(Spec S) ≅ S`. -/
theorem affinePointsEquiv_eq_map_pointsEquiv' (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    affinePointsEquiv n R S x =
      Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (pointsEquiv n R _ x) := by
  rw [pointsEquiv_eq_affinePointsEquiv, ← Corepresented.affineSectionsIso_hom_ringHom]
  ext i j
  exact (ConcreteCategory.congr_hom (Corepresented.affineSectionsIso S).inv_hom_id _).symm

/-- The matrices of a diagonal cocharacter are the diagonal matrices of powers. -/
theorem cocharacterUnitsHom_diagonalCocharacter (e : n → ℤ) (u : Aˣ) :
    cocharacterUnitsHom (diagonalCocharacter n R e) A u = diagonalUnits A e u := by
  rw [cocharacterUnitsHom_apply, affinePointsEquiv_eq_map_pointsEquiv',
    pointsEquiv_diagonalCocharacter]
  erw [map_diagonalUnits]
  congr 1
  exact MulEquiv.apply_symm_apply (Gm.algebraPointsEquiv A) u

variable (R) in
omit [Fintype n] [DecidableEq n] in
/-- The universal point of `𝔾_m` is the algebra point of the Laurent coordinate. -/
theorem universalPoint_eq_algebraPointsEquiv_symm :
    Gm.universalPoint R =
      (Gm.algebraPointsEquiv (LaurentPolynomial R)).symm (cocharacterLaurentUnit R) := by
  apply (Gm.algebraPointsEquiv (LaurentPolynomial R)).injective
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  exact Gm.affinePointsEquiv_universalPoint R

/-- A cocharacter of `GL_n` is determined by its matrix at the Laurent coordinate. -/
theorem eq_of_weightMatrix_eq {ψ : (Gm (Spec R)).toGrp ⟶ groupScheme n R}
    (h : weightMatrix χ = weightMatrix ψ) : χ = ψ := by
  apply Gm.hom_ext_universalPoint R
  apply (affinePointsEquiv n R (CommAlgCat.of R (LaurentPolynomial R))).injective
  rw [universalPoint_eq_algebraPointsEquiv_symm]
  exact h

variable (R) in
/-- The base point of `GL_n` with a given invertible matrix over `R`. -/
def baseOfMatrix (g : GL n R) : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme n R).X :=
  (pointsEquiv n R (Over.mk (𝟙 (Spec R)))).symm
    (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).inv.hom g)

/-- The constant points of `baseOfMatrix g` over a test algebra have the matrix `g`. -/
theorem affinePointsEquiv_constantPoint_baseOfMatrix (g : GL n R) :
    affinePointsEquiv n R (CommAlgCat.of R A)
        (constantPoint (groupScheme n R) (baseOfMatrix R g)
          ((algSpec R).obj (op (CommAlgCat.of R A)))) =
      Matrix.GeneralLinearGroup.map (algebraMap R A) g := by
  rw [affinePointsEquiv_eq_map_pointsEquiv', constantPoint, pointsEquiv_naturality,
    baseOfMatrix, MulEquiv.apply_symm_apply]
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A)))
    ((Scheme.ΓSpecIso R).inv ((g : Matrix n n R) i j))
  refine h.trans ?_
  change algebraMap R A (((Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom)
    ((g : Matrix n n R) i j)) = _
  rw [Iso.inv_hom_id]
  rfl

end Comparison

/-! ### Diagonalization over a field -/

section Diagonalization

omit [Fintype n] [DecidableEq n] in
theorem cocharacterLaurentUnit_zpow (m : ℤ) :
    ((cocharacterLaurentUnit R ^ m : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T m := by
  induction m using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ m ih =>
      rw [zpow_add_one, Units.val_mul, ih, cocharacterLaurentUnit_val, ← LaurentPolynomial.T_add]
  | pred m ih =>
      have hinv : ((cocharacterLaurentUnit R)⁻¹ : (LaurentPolynomial R)ˣ) =
          (LaurentPolynomial.T (-1) : LaurentPolynomial R) := by
        apply Units.inv_eq_of_mul_eq_one_right
        rw [cocharacterLaurentUnit_val, ← LaurentPolynomial.T_add]
        simp [LaurentPolynomial.T_zero]
      rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add]
      congr 1

/-- Conjugating a cocharacter by a base point conjugates its matrix at the Laurent
coordinate. -/
theorem weightMatrix_innerIso (g : GL n R) :
    weightMatrix (χ ≫ (innerIso (groupScheme n R) (baseOfMatrix R g)).hom) =
      Matrix.GeneralLinearGroup.map (algebraMap R (LaurentPolynomial R)) g * weightMatrix χ *
        (Matrix.GeneralLinearGroup.map (algebraMap R (LaurentPolynomial R)) g)⁻¹ := by
  rw [weightMatrix, cocharacterUnitsHom_apply, Grp.comp_hom_hom, ← Category.assoc,
    comp_innerIso_hom, map_mul, map_mul, map_inv, affinePointsEquiv_constantPoint_baseOfMatrix]
  rfl

theorem weightMatrix_diagonalCocharacter (e : n → ℤ) :
    weightMatrix (diagonalCocharacter n R e) =
      diagonalUnits (LaurentPolynomial R) e (cocharacterLaurentUnit R) :=
  cocharacterUnitsHom_diagonalCocharacter e _

end Diagonalization

section Field

variable {K : Type u} [Field K]
  (ψ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ groupScheme n (CommRingCat.of K))

/-- Over a field, every cocharacter of `GL_n` is conjugate by a base point to a diagonal
cocharacter. -/
theorem exists_matrix_innerIso_comp_eq_diagonalCocharacter :
    ∃ (g : GL n K) (e : n → ℤ),
      ψ ≫ (innerIso (groupScheme n (CommRingCat.of K)) (baseOfMatrix (CommRingCat.of K) g)).hom =
        diagonalCocharacter n (CommRingCat.of K) e := by
  classical
  obtain ⟨P, e, hP⟩ := Langlands.LinearAlgebra.exists_conj_eq_diagonal_of_orthogonal (K := K)
    (weightProjector ψ) (fun a b => by
      rw [weightProjector_mul]
      split_ifs with h
      · rw [h]
      · rfl) (cocharacterWeightSupport ψ) (sum_weightProjector ψ)
  refine ⟨P⁻¹, e, eq_of_weightMatrix_eq _ ?_⟩
  rw [weightMatrix_innerIso, weightMatrix_diagonalCocharacter]
  have he : ∀ i, e i ∈ cocharacterWeightSupport ψ := by
    intro i
    by_contra hi
    have h := congrFun (congrFun (hP (e i)) i) i
    rw [weightProjector_eq_zero ψ hi, Matrix.mul_zero, Matrix.zero_mul] at h
    simp at h
  set φ := algebraMap K (LaurentPolynomial K)
  have hM : (weightMatrix ψ : Matrix n n (LaurentPolynomial K)) =
      ∑ a ∈ cocharacterWeightSupport ψ,
        (LaurentPolynomial.T a : LaurentPolynomial K) • (weightProjector ψ a).map φ := by
    refine Matrix.ext fun i j => ?_
    rw [weightMatrix_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    change AddMonoidAlgebra.single a (weightProjector ψ a i j) = _
    rw [LaurentPolynomial.single_eq_C_mul_T (R := K), mul_comm]
    rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, inv_inv, coe_diagonalUnits]
  change (P⁻¹ : GL n K).val.map φ * (weightMatrix ψ : Matrix n n (LaurentPolynomial K)) *
    (P : GL n K).val.map φ = _
  rw [hM, Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ a, (P⁻¹ : GL n K).val.map φ *
      ((LaurentPolynomial.T a : LaurentPolynomial K) • (weightProjector ψ a).map φ) *
      (P : GL n K).val.map φ =
        (LaurentPolynomial.T a : LaurentPolynomial K) •
          Matrix.diagonal (fun i => φ (if e i = a then 1 else 0)) := by
    intro a
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, hP a,
      Matrix.diagonal_map (map_zero φ)]
  simp only [hterm]
  ext i j
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij
    rw [cocharacterLaurentUnit_zpow]
    simp only [apply_ite φ, map_one, map_zero, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (cocharacterWeightSupport ψ) (e i)]
    simp [he i]
  · simp

end Field

end GeneralLinear

end Langlands.GroupScheme
