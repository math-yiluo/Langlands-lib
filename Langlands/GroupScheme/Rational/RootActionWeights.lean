import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers

/-! # Root-group coefficient operators and actual torus weights -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme

namespace VectorGroup

variable {R : CommRingCat.{u}}

/-- On an affine test, the scalar section parameter is the usual affine parameter. -/
theorem affinePoint_eq_scalarPoint (A : CommAlgCat.{u} R) (c : A) :
    affinePoint (d := 1) A (fun _ => c) =
      scalarPoint R ((algSpec R).obj (op A))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) := by
  apply (coordinates R 1 _).injective
  rw [scalarPoint, MulEquiv.apply_symm_apply]
  change Corepresented.pointsEquiv (functor R 1) (corepresentableBy R 1) _ _ = _
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv, affinePointsEquiv_affinePoint]
  rfl

/-- Global-section character values and affine character values agree. -/
theorem charValue_affine {T : CommGroupScheme (Spec R)} (α : characterLattice T)
    (A : CommAlgCat.{u} R) (t : GroupScheme.affinePoints T.toGrp A) :
    charValue α ((algSpec R).obj (op A)) t =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (Lie.characterValue α t : A) := by
  change charValue α ((algSpec R).obj (op A)) t =
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (charValue α ((algSpec R).obj (op A)) t))
  simp

end VectorGroup

namespace SplitPinning.NormalizedRootParametrization

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {a : p.base.support}
    (x : p.NormalizedRootParametrization a)

/-- The supplied full-torus conjugation law in actual affine additive coordinates. -/
theorem affinePoint_conjugation (A : CommAlgCat.{u} k) (t : GroupScheme.affinePoints p.torus.toGrp A)
    (c : A) :
    (t ≫ p.inclusion.hom.hom) *
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ : Fin 1 => c) ≫ x.hom.hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ =
      VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
        (fun _ : Fin 1 => (Lie.characterValue (p.rootDatum.root a) t : A) * c) ≫
          x.hom.hom.hom := by
  rw [VectorGroup.affinePoint_eq_scalarPoint,
    VectorGroup.affinePoint_eq_scalarPoint, map_mul,
    ← VectorGroup.charValue_affine (p.rootDatum.root a) A t]
  exact x.torus_equivariant _ t ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c)

variable {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- Actual representation matrices inherit the supplied affine root conjugation law. -/
theorem affineMatrix_root_commutation (A : CommAlgCat.{u} k)
    (t : GroupScheme.affinePoints p.torus.toGrp A) (c : A) :
    (ρ.restrict p.inclusion).affineMatrix A t *
        (ρ.restrict x.hom).affineMatrix A (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c)) =
      (ρ.restrict x.hom).affineMatrix A
          (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
            (fun _ => (Lie.characterValue (p.rootDatum.root a) t : A) * c)) *
        (ρ.restrict p.inclusion).affineMatrix A t := by
  have h := congrArg (ρ.affineMatrix A) (x.affinePoint_conjugation A t c)
  simp only [map_mul, map_inv] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

end SplitPinning.NormalizedRootParametrization

namespace MatrixRepresentation.AdditiveDividedPowers

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Scaling the variable multiplies its degree-m coefficient by the m-th power. -/
theorem coeff_aeval_C_mul_X (P : k[X]) (c : A) (m : ℕ) :
    (Polynomial.aeval (Polynomial.C c * Polynomial.X : A[X]) P).coeff m =
      algebraMap k A (P.coeff m) * c ^ m := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.coeff_add, hP, hQ, add_mul]
  | monomial d b =>
    simp only [Polynomial.aeval_monomial, Polynomial.algebraMap_apply, mul_pow,
      ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    split_ifs <;> simp_all

end MatrixRepresentation.AdditiveDividedPowers

namespace SplitPinning.NormalizedRootParametrization

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {a : p.base.support}
    (x : p.NormalizedRootParametrization a)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- Each coefficient matrix has torus conjugation weight m times the root. -/
theorem coefficientMatrix_root_commutation (A : CommAlgCat.{u} k)
    (t : GroupScheme.affinePoints p.torus.toGrp A) (m : ℕ) :
    ((ρ.restrict p.inclusion).affineMatrix A t : Matrix n n A) *
        (coefficientMatrix (ρ.restrict x.hom) m).map (algebraMap k A) =
      (Lie.characterValue (p.rootDatum.root a) t : A) ^ m •
        ((coefficientMatrix (ρ.restrict x.hom) m).map (algebraMap k A) *
          ((ρ.restrict p.inclusion).affineMatrix A t : Matrix n n A)) := by
  let S : CommAlgCat.{u} k := CommAlgCat.of k A[X]
  let f : A →ₐ[k] A[X] := Polynomial.CAlgHom
  let t' : GroupScheme.affinePoints p.torus.toGrp S :=
    GroupScheme.affinePointMap p.torus.toGrp (CommAlgCat.ofHom f) t
  have hT : ((ρ.restrict p.inclusion).affineMatrix S t' : Matrix n n A[X]) =
      (((ρ.restrict p.inclusion).affineMatrix A t : Matrix n n A).map Polynomial.C) :=
    congrArg Units.val ((ρ.restrict p.inclusion).affineMatrix_naturality
      (CommAlgCat.ofHom f) t)
  have hα : (Lie.characterValue (p.rootDatum.root a) t' : A[X]) =
      Polynomial.C (Lie.characterValue (p.rootDatum.root a) t : A) := by
    exact congrArg Units.val (Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
      (CommAlgCat.ofHom f) (t ≫ (CommGroupScheme.groupHom (p.rootDatum.root a)).hom.hom))
  have h := congrArg Units.val (x.affineMatrix_root_commutation ρ S t' Polynomial.X)
  simp only [Units.val_mul] at h
  rw [hT, ← univariateMatrix_aeval, ← univariateMatrix_aeval, hα] at h
  dsimp only [S] at h
  ext i j
  have hij := congrArg (fun M : Matrix n n A[X] => (M i j).coeff m) h
  simp only [Matrix.mul_apply, Matrix.map_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Polynomial.aeval_X_left_eq_map, Polynomial.coeff_map, coeff_aeval_C_mul_X] at hij
  change (∑ l, ((ρ.restrict p.inclusion).affineMatrix A t : Matrix n n A) i l *
      algebraMap k A ((univariateMatrix (ρ.restrict x.hom) l j).coeff m)) = _
  rw [hij]
  change (∑ l, algebraMap k A ((univariateMatrix (ρ.restrict x.hom) i l).coeff m) *
      (Lie.characterValue (p.rootDatum.root a) t : A) ^ m *
        ((ρ.restrict p.inclusion).affineMatrix A t : Matrix n n A) l j) = _
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.map_apply, coefficientMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- The actual degree-m root operator sends weight mu to weight mu + m alpha. -/
theorem dividedPower_mem_representationWeightSpace (m : ℕ)
    {lam : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ lam) :
    dividedPower (ρ.restrict x.hom) m v ∈
      p.representationWeightSpace ρ (lam + m • p.rootDatum.root a) := by
  let := p.isSplitTorus.isAffineHom
  let A := CharacterUnits.Coord p.torus.toGrp
  let H := ρ.restrict p.inclusion
  let B := coefficientMatrix (ρ.restrict x.hom) m
  let χ : rationalCharacters p.torus.toGrp :=
    (rationalCharacters.equivCharacterLattice p.torus).symm lam
  let α : rationalCharacters p.torus.toGrp :=
    (rationalCharacters.equivCharacterLattice p.torus).symm (p.rootDatum.root a)
  let φ : k →+* A := algebraMap k A
  have hmap : MatrixRepresentation.universalVector (B *ᵥ v) =
      B.map φ *ᵥ MatrixRepresentation.universalVector v := by
    funext i
    exact φ.map_mulVec B v i
  have hcov := x.coefficientMatrix_root_commutation ρ
    (CommAlgCat.of k A) (CharacterUnits.universalPoint p.torus.toGrp) m
  change H.universalCharacterMatrix * B.map φ =
    (CharacterUnits.unit α : A) ^ m •
      (B.map φ * H.universalCharacterMatrix) at hcov
  change H.universalCharacterMatrix *ᵥ MatrixRepresentation.universalVector v =
    (CharacterUnits.unit χ : A) • MatrixRepresentation.universalVector v at hv
  have hn (d : ℕ) : CharacterUnits.unit (d • α) = CharacterUnits.unit α ^ d := by
    induction d with
    | zero => rw [zero_nsmul, CharacterUnits.unit_zero, pow_zero]
    | succ m ih => rw [succ_nsmul, CharacterUnits.unit_add, ih, pow_succ]
  have hu : (CharacterUnits.unit (χ + m • α) : A) =
      (CharacterUnits.unit α : A) ^ m * (CharacterUnits.unit χ : A) := by
    rw [CharacterUnits.unit_add, hn, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm]
  rw [dividedPower_eq_toLin]
  change H.universalCharacterMatrix *ᵥ MatrixRepresentation.universalVector (B *ᵥ v) =
    (CharacterUnits.unit (χ + m • α) : A) • MatrixRepresentation.universalVector (B *ᵥ v)
  rw [hmap, Matrix.mulVec_mulVec, hcov, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, smul_smul, hu]

/-- The actual root coefficient operator restricted to the corresponding torus weights. -/
def weightRaisingOperator (m : ℕ) (lam : characterLattice p.torus) :
    p.representationWeightSpace ρ lam →ₗ[k]
      p.representationWeightSpace ρ (lam + m • p.rootDatum.root a) where
  toFun v := ⟨dividedPower (ρ.restrict x.hom) m v,
    x.dividedPower_mem_representationWeightSpace ρ m v.property⟩
  map_add' v w := Subtype.ext (map_add (dividedPower (ρ.restrict x.hom) m) (v : n → k) w)
  map_smul' c v := Subtype.ext (map_smul (dividedPower (ρ.restrict x.hom) m) c (v : n → k))

@[simp] theorem weightRaisingOperator_apply (m : ℕ) (lam : characterLattice p.torus)
    (v : p.representationWeightSpace ρ lam) :
    (x.weightRaisingOperator ρ m lam v : n → k) =
      dividedPower (ρ.restrict x.hom) m v := rfl

/-- If the shifted weight does not occur, the corresponding root coefficient vanishes. -/
theorem dividedPower_eq_zero_of_weightSpace_eq_bot (m : ℕ)
    {lam : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ lam)
    (hbot : p.representationWeightSpace ρ (lam + m • p.rootDatum.root a) = ⊥) :
    dividedPower (ρ.restrict x.hom) m v = 0 := by
  have h := x.dividedPower_mem_representationWeightSpace ρ m hv
  rw [hbot, Submodule.mem_bot] at h
  exact h

end SplitPinning.NormalizedRootParametrization
end Langlands.GroupScheme
