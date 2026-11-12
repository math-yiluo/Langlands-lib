import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Torus.RelativeAdjointWeights
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Diagonalization of cocharacters of the general linear group over a principal ideal domain -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CocharacterDiagonal

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {n : Type} [Fintype n] [DecidableEq n] (I : Type u) [Fintype I] [DecidableEq I]
  (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of R)) I) n)

/-- The span of the universal coefficient columns of exponent `m`. -/
def weightColumns (m : I → ℤ) : Submodule R (n → R) :=
  Submodule.span R (Set.range fun j => coefficientColumn I ρ m j)

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Every element of the span of the coefficient columns of exponent `m` is a weight vector of
weight `m` after every coefficient extension. -/
theorem weight_of_mem_weightColumns {m : I → ℤ} {v : n → R} (hv : v ∈ weightColumns I ρ m)
    (A : Type u) [CommRing A] [Algebra R A] (t : I → Aˣ) :
    (matrixAt I ρ t : Matrix n n A) *ᵥ (fun a => algebraMap R A (v a)) =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) •
        (fun a => algebraMap R A (v a)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact coefficientColumn_weight I ρ t m j
  | zero =>
    simp only [Pi.zero_apply, map_zero]
    rw [show (fun _ : n => (0 : A)) = 0 from rfl, mulVec_zero, smul_zero]
  | add x y _ _ hx hy =>
    have hxy : (fun a => algebraMap R A ((x + y) a)) =
        (fun a => algebraMap R A (x a)) + (fun a => algebraMap R A (y a)) := by
      funext a
      simp
    rw [hxy, mulVec_add, hx, hy, smul_add]
  | smul r x _ hx =>
    have hrx : (fun a => algebraMap R A ((r • x) a)) =
        algebraMap R A r • (fun a => algebraMap R A (x a)) := by
      funext a
      simp
    rw [hrx, mulVec_smul, hx, smul_comm]

/-- The universal family of monomial units. -/
abbrev universalUnits : I → (AddMonoidAlgebra R (I → ℤ))ˣ :=
  fun i => splitTorus.exponentUnit (R := CommRingCat.of R) I (Pi.single i 1)

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem exponentValue_universalUnits (m : I → ℤ) :
    splitTorus.exponentValue I (universalUnits (R := R) I) (Multiplicative.ofAdd m) =
      splitTorus.exponentUnit (R := CommRingCat.of R) I m := by
  have h := splitTorus.exponentValue_universalPoint_ring (R := CommRingCat.of R) I m
  rw [splitTorus.algebraPointsEquiv_universalPoint] at h
  exact h

/-- The universal translate of a column vector. -/
def translateVec (v : n → R) : n → AddMonoidAlgebra R (I → ℤ) :=
  (matrixAt I ρ (universalUnits (R := R) I) : Matrix n n (AddMonoidAlgebra R (I → ℤ))) *ᵥ
    (fun b => algebraMap R (AddMonoidAlgebra R (I → ℤ)) (v b))

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem translateVec_add (v w : n → R) :
    translateVec I ρ (v + w) = translateVec I ρ v + translateVec I ρ w := by
  have hvw : (fun b => algebraMap R (AddMonoidAlgebra R (I → ℤ)) ((v + w) b)) =
      (fun b => algebraMap R _ (v b)) + (fun b => algebraMap R _ (w b)) := by
    funext b
    simp
  rw [translateVec, hvw, mulVec_add]
  rfl

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem translateVec_smul (r : R) (v : n → R) :
    translateVec I ρ (r • v) = algebraMap R (AddMonoidAlgebra R (I → ℤ)) r • translateVec I ρ v := by
  have hrv : (fun b => algebraMap R (AddMonoidAlgebra R (I → ℤ)) ((r • v) b)) =
      algebraMap R (AddMonoidAlgebra R (I → ℤ)) r • (fun b => algebraMap R _ (v b)) := by
    funext b
    simp
  rw [translateVec, hrv, mulVec_smul]
  rfl

/-- The coefficient at exponent `m` of the universal translate of a column vector. -/
def weightProjection (m : I → ℤ) : (n → R) →ₗ[R] (n → R) where
  toFun v a := (translateVec I ρ v a).coeff m
  map_add' v w := by
    funext a
    rw [translateVec_add]
    rfl
  map_smul' r v := by
    funext a
    rw [translateVec_smul]
    exact AddMonoidAlgebra.coeff_single_zero_mul _ r m

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem weightProjection_of_mem {m m' : I → ℤ} {v : n → R}
    (hv : v ∈ weightColumns I ρ m') :
    weightProjection I ρ m v = if m' = m then v else 0 := by
  funext a
  have h := congrFun (weight_of_mem_weightColumns I ρ hv (AddMonoidAlgebra R (I → ℤ))
    (universalUnits (R := R) I)) a
  change (translateVec I ρ v a).coeff m = _
  rw [translateVec, h, exponentValue_universalUnits]
  simp only [Pi.smul_apply, smul_eq_mul, splitTorus.exponentUnit_val]
  rw [show algebraMap R (AddMonoidAlgebra R (I → ℤ)) (v a) =
    AddMonoidAlgebra.single 0 (v a) from rfl, AddMonoidAlgebra.single_mul_single, add_zero,
    one_mul]
  split_ifs with hmm
  · subst hmm
    simp
  · simp [AddMonoidAlgebra.coeff_single, Ne.symm hmm]

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem iSupIndep_weightColumns : iSupIndep (weightColumns (R := R) I ρ) := by
  classical
  rw [iSupIndep_def]
  intro m
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hker : (⨆ (m' : I → ℤ) (_ : m' ≠ m), weightColumns I ρ m') ≤
      LinearMap.ker (weightProjection I ρ m) := by
    refine iSup₂_le fun m' hm' w hw => ?_
    rw [LinearMap.mem_ker, weightProjection_of_mem I ρ hw, ite_eq_right_iff.mpr (fun h => absurd h hm')]
  have h1 := weightProjection_of_mem I ρ (m := m) hv
  rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h1
  rw [← h1]
  exact hker hv'

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem iSup_weightColumns : ⨆ m, weightColumns (R := R) I ρ m = ⊤ := by
  apply top_unique
  rw [← span_coefficientColumn I ρ, Submodule.span_le]
  rintro _ ⟨⟨m, j⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem m (Submodule.subset_span ⟨j, rfl⟩)

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem isInternal_weightColumns : DirectSum.IsInternal (weightColumns (R := R) I ρ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_weightColumns I ρ)
    (iSup_weightColumns I ρ)

/-- Over a principal ideal domain there is a basis of weight vectors. -/
theorem exists_weightBasis :
    ∃ (b : Basis n R (n → R)) (w : n → (I → ℤ)), ∀ j, b j ∈ weightColumns I ρ (w j) := by
  classical
  let v : ∀ m, Basis (Fin (Submodule.basisOfPid (Pi.basisFun R n) (weightColumns I ρ m)).1) R
      (weightColumns I ρ m) := fun m =>
    (Submodule.basisOfPid (Pi.basisFun R n) (weightColumns I ρ m)).2
  let c := (isInternal_weightColumns I ρ).collectedBasis v
  let eqv := c.indexEquiv (Pi.basisFun R n)
  refine ⟨c.reindex eqv, fun j => (eqv.symm j).1, fun j => ?_⟩
  rw [Basis.reindex_apply]
  exact (isInternal_weightColumns I ρ).collectedBasis_mem v _

/-- A single invertible matrix over a principal ideal domain diagonalizes the representation on
every test algebra. -/
theorem exists_diagonalizingMatrix_of_isPrincipalIdealRing :
    ∃ (B : GL n R) (w : n → (I → ℤ)),
      ∀ (A : Type u) [CommRing A] [Algebra R A] (t : I → Aˣ),
        (Matrix.GeneralLinearGroup.map (algebraMap R A) B)⁻¹ *
            matrixAt I ρ t * Matrix.GeneralLinearGroup.map (algebraMap R A) B =
          diagonalMatrix
            (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j))) := by
  classical
  obtain ⟨b, w, hb⟩ := exists_weightBasis I ρ
  let std := Pi.basisFun R n
  let B : GL n R :=
    ⟨std.toMatrix b, b.toMatrix std,
      std.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip std⟩
  have hB (a j : n) : (B : Matrix n n R) a j = b j a := by
    simp [B, Basis.toMatrix_apply, std]
  refine ⟨B, w, ?_⟩
  intro A _ _ t
  let C := Matrix.GeneralLinearGroup.map (algebraMap R A) B
  let D := diagonalMatrix
    (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j)))
  have hc : matrixAt I ρ t * C = C * D := by
    apply Units.ext
    ext a j
    have hj := congrFun (weight_of_mem_weightColumns I ρ (hb j) A t) a
    change ((matrixAt I ρ t : Matrix n n A) * (C : Matrix n n A)) a j =
      ((C : Matrix n n A) * Matrix.diagonal
        (fun r => (splitTorus.exponentValue I t (Multiplicative.ofAdd (w r)) : A))) a j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, C, Matrix.GeneralLinearGroup.map_apply, hB]
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using hj
  change C⁻¹ * matrixAt I ρ t * C = D
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

end CocharacterDiagonal

/-- Every cocharacter of a general linear group over a principal ideal domain is conjugate by
a point over that ring to a diagonal cocharacter. -/
theorem exists_innerIso_comp_eq_diagonalCocharacter_of_isPrincipalIdealRing
    (k : Type u) [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
    {n : Type} [Fintype n] [DecidableEq n]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme n (CommRingCat.of k)) :
    ∃ (B : GL n k) (e : n → ℤ),
      χ ≫ ((groupScheme n (CommRingCat.of k)).innerIso
          (CocharacterDiagonal.rationalMatrixPoint (R := CommRingCat.of k) B)).hom =
        diagonalCocharacter n (CommRingCat.of k) e := by
  classical
  let R := CommRingCat.of k
  let ρ : MatrixRepresentation (splitTorus (Spec R) PUnit) n :=
    (splitTorus.gmIso (Spec R)).inv ≫ χ
  have hρ : (splitTorus.gmIso (Spec R)).hom ≫ ρ = χ := by
    dsimp only [ρ]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  obtain ⟨B, w, hw⟩ :=
    CocharacterDiagonal.exists_diagonalizingMatrix_of_isPrincipalIdealRing (R := k) PUnit ρ
  refine ⟨B⁻¹, fun j => w j PUnit.unit, ?_⟩
  apply Gm.hom_ext_universalPoint R
  let A : CommAlgCat R := CommAlgCat.of R (LaurentPolynomial k)
  let x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X := Gm.universalPoint R
  let t := splitTorus.algebraPointsEquiv PUnit (LaurentPolynomial k)
    (x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom)
  have hm : CocharacterDiagonal.matrixAt PUnit ρ t =
      affinePointsEquiv n R A (x ≫ χ.hom.hom) := by
    dsimp only [CocharacterDiagonal.matrixAt, t]
    rw [MulEquiv.symm_apply_apply, MatrixRepresentation.affineMatrix_apply, Category.assoc]
    change affinePointsEquiv n R A
      (x ≫ ((splitTorus.gmIso (Spec R)).hom ≫ ρ).hom.hom) = _
    rw [hρ]
  have ht : t = fun _ => Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x :=
    CocharacterDiagonal.algebraPointsEquiv_comp_gmIso x
  apply (affinePointsEquiv n R A).injective
  change affinePointsEquiv n R A
      ((x ≫ χ.hom.hom) ≫
        ((groupScheme n R).innerIso
          (CocharacterDiagonal.rationalMatrixPoint B⁻¹)).hom.hom.hom) = _
  rw [comp_innerIso_hom, map_mul, map_mul, map_inv,
    CocharacterDiagonal.affinePointsEquiv_constant_rationalMatrixPoint,
    CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  simp only [map_inv, inv_inv]
  have h := hw (LaurentPolynomial k) t
  rw [hm] at h
  rw [ht] at h
  simpa [A, x, R, splitTorus.exponentValue, CocharacterDiagonal.diagonalMatrix,
    diagonalUnits, MonoidHom.pi] using h

end Langlands.GroupScheme.GeneralLinear
