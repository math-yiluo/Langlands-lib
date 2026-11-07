import Langlands.GroupScheme.Rational.RootActionWeights

/-! # Character shifts for arbitrary torus-equivariant additive actions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme

namespace VectorGroup

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The scalar all-test conjugation law for an arbitrary supplied additive map.
The character may have either sign; no root-subgroup or existence claim is made. -/
def IsTorusEquivariant (i : T.toGrp ⟶ G)
    (x : groupScheme (CommRingCat.of k) 1 ⟶ G) (α : characterLattice T) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X) (c : Γ(Z.left, ⊤)),
    (t ≫ i.hom.hom) * (scalarPoint (CommRingCat.of k) Z c ≫ x.hom.hom) *
        (t ≫ i.hom.hom)⁻¹ =
      scalarPoint (CommRingCat.of k) Z (charValue α Z t * c) ≫ x.hom.hom

namespace IsTorusEquivariant

variable {i : T.toGrp ⟶ G}
    {x : groupScheme (CommRingCat.of k) 1 ⟶ G} {α : characterLattice T}
    (hx : IsTorusEquivariant i x α)

include hx

/-- The supplied conjugation law expressed in actual affine additive coordinates. -/
theorem affinePoint_conjugation (A : CommAlgCat.{u} k)
    (t : GroupScheme.affinePoints T.toGrp A) (c : A) :
    (t ≫ i.hom.hom) *
        (affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ : Fin 1 => c) ≫ x.hom.hom) *
        (t ≫ i.hom.hom)⁻¹ =
      affinePoint (R := CommRingCat.of k) (d := 1) A
        (fun _ : Fin 1 => (Lie.characterValue α t : A) * c) ≫ x.hom.hom := by
  rw [affinePoint_eq_scalarPoint, affinePoint_eq_scalarPoint, map_mul,
    ← charValue_affine α A t]
  exact hx _ t ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c)

variable {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- Actual representation matrices inherit the affine conjugation law. -/
theorem affineMatrix_commutation (A : CommAlgCat.{u} k)
    (t : GroupScheme.affinePoints T.toGrp A) (c : A) :
    (ρ.restrict i).affineMatrix A t *
        (ρ.restrict x).affineMatrix A
          (affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c)) =
      (ρ.restrict x).affineMatrix A
          (affinePoint (R := CommRingCat.of k) (d := 1) A
            (fun _ => (Lie.characterValue α t : A) * c)) *
        (ρ.restrict i).affineMatrix A t := by
  have h := congrArg (ρ.affineMatrix A) (hx.affinePoint_conjugation A t c)
  simp only [map_mul, map_inv] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

open MatrixRepresentation.AdditiveDividedPowers

/-- Every original coefficient matrix has the corresponding multiple of the
supplied character as its conjugation weight, over every test algebra. -/
theorem coefficientMatrix_commutation (A : CommAlgCat.{u} k)
    (t : GroupScheme.affinePoints T.toGrp A) (m : ℕ) :
    ((ρ.restrict i).affineMatrix A t : Matrix n n A) *
        (coefficientMatrix (ρ.restrict x) m).map (algebraMap k A) =
      (Lie.characterValue α t : A) ^ m •
        ((coefficientMatrix (ρ.restrict x) m).map (algebraMap k A) *
          ((ρ.restrict i).affineMatrix A t : Matrix n n A)) := by
  let S : CommAlgCat.{u} k := CommAlgCat.of k A[X]
  let f : A →ₐ[k] A[X] := Polynomial.CAlgHom
  let t' : GroupScheme.affinePoints T.toGrp S :=
    GroupScheme.affinePointMap T.toGrp (CommAlgCat.ofHom f) t
  have hT : ((ρ.restrict i).affineMatrix S t' : Matrix n n A[X]) =
      (((ρ.restrict i).affineMatrix A t : Matrix n n A).map Polynomial.C) :=
    congrArg Units.val ((ρ.restrict i).affineMatrix_naturality (CommAlgCat.ofHom f) t)
  have hα : (Lie.characterValue α t' : A[X]) =
      Polynomial.C (Lie.characterValue α t : A) := by
    exact congrArg Units.val (Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
      (CommAlgCat.ofHom f) (t ≫ (CommGroupScheme.groupHom α).hom.hom))
  have h := congrArg Units.val (hx.affineMatrix_commutation ρ S t' Polynomial.X)
  simp only [Units.val_mul] at h
  rw [hT, ← univariateMatrix_aeval, ← univariateMatrix_aeval, hα] at h
  dsimp only [S] at h
  ext a b
  have hab := congrArg (fun M : Matrix n n A[X] => (M a b).coeff m) h
  simp only [Matrix.mul_apply, Matrix.map_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Polynomial.aeval_X_left_eq_map, Polynomial.coeff_map, coeff_aeval_C_mul_X] at hab
  change (∑ l, ((ρ.restrict i).affineMatrix A t : Matrix n n A) a l *
      algebraMap k A ((univariateMatrix (ρ.restrict x) l b).coeff m)) = _
  rw [hab]
  change (∑ l, algebraMap k A ((univariateMatrix (ρ.restrict x) a l).coeff m) *
      (Lie.characterValue α t : A) ^ m *
        ((ρ.restrict i).affineMatrix A t : Matrix n n A) l b) = _
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.map_apply, coefficientMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

variable [IsAffineHom T.toGrp.X.hom]

/-- The original degree-m operator shifts an actual all-algebra character
space by m times the supplied character, of either sign. -/
theorem dividedPower_mem_characterSpace (m : ℕ)
    {χ : rationalCharacters T.toGrp} {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ) :
    dividedPower (ρ.restrict x) m v ∈
      (ρ.restrict i).characterSpace
        (χ + m • (rationalCharacters.equivCharacterLattice T).symm α) := by
  let A := CharacterUnits.Coord T.toGrp
  let H := ρ.restrict i
  let B := coefficientMatrix (ρ.restrict x) m
  let β : rationalCharacters T.toGrp :=
    (rationalCharacters.equivCharacterLattice T).symm α
  let φ : k →+* A := algebraMap k A
  have hmap : MatrixRepresentation.universalVector (B *ᵥ v) =
      B.map φ *ᵥ MatrixRepresentation.universalVector v := by
    funext a
    exact φ.map_mulVec B v a
  have hcov := hx.coefficientMatrix_commutation ρ
    (CommAlgCat.of k A) (CharacterUnits.universalPoint T.toGrp) m
  change H.universalCharacterMatrix * B.map φ =
    (CharacterUnits.unit β : A) ^ m •
      (B.map φ * H.universalCharacterMatrix) at hcov
  change H.universalCharacterMatrix *ᵥ MatrixRepresentation.universalVector v =
    (CharacterUnits.unit χ : A) • MatrixRepresentation.universalVector v at hv
  have hn (d : ℕ) : CharacterUnits.unit (d • β) = CharacterUnits.unit β ^ d := by
    induction d with
    | zero => rw [zero_nsmul, CharacterUnits.unit_zero, pow_zero]
    | succ d ih => rw [succ_nsmul, CharacterUnits.unit_add, ih, pow_succ]
  have hu : (CharacterUnits.unit (χ + m • β) : A) =
      (CharacterUnits.unit β : A) ^ m * (CharacterUnits.unit χ : A) := by
    rw [CharacterUnits.unit_add, hn, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm]
  rw [dividedPower_eq_toLin]
  change H.universalCharacterMatrix *ᵥ MatrixRepresentation.universalVector (B *ᵥ v) =
    (CharacterUnits.unit (χ + m • β) : A) • MatrixRepresentation.universalVector (B *ᵥ v)
  rw [hmap, Matrix.mulVec_mulVec, hcov, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, smul_smul, hu]

end IsTorusEquivariant
end VectorGroup

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}
    {x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    {α : characterLattice p.torus}

/-- Specialization to the supplied pinning's weight-space notation. -/
theorem dividedPower_mem_representationWeightSpace_of_equivariant
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x α)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    (m : ℕ) {mu : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ mu) :
    MatrixRepresentation.AdditiveDividedPowers.dividedPower (ρ.restrict x) m v ∈
      p.representationWeightSpace ρ (mu + m • α) := by
  let := p.isSplitTorus.isAffineHom
  exact hx.dividedPower_mem_characterSpace ρ m hv

end SplitPinning
end Langlands.GroupScheme
