import Langlands.GroupScheme.MatrixRepresentation.SplitTorusEigenbasis
import Langlands.GroupScheme.MatrixRepresentation.NormalKernel

/-! # Diagonalizing a cocharacter while retaining its actual coordinate eigenline -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual all-algebra power action on one coordinate vector. -/
def HasCoordinatePowerAction
    (σ : MatrixRepresentation (Gm (Spec (CommRingCat.of k))).toGrp n)
    (j : n) (m : ℤ) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A]
    (x : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of k))).toGrp (CommAlgCat.of k A)),
    (σ.affineMatrix (CommAlgCat.of k A) x : Matrix n n A) *ᵥ Pi.single j 1 =
      ((Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k A) x ^ m : Aˣ) : A) •
        (Pi.single j 1 : n → A)

/-- The integer of the actual algebraic character on a coordinate Gm eigenline. -/
def coordinateLineCocharacterWeight
    (σ : MatrixRepresentation (Gm (Spec (CommRingCat.of k))).toGrp n)
    (j : n) (hline : σ.PreservesCoordinateLine j) : ℤ :=
  gmEndEquiv k ((rationalCharacters.equivCharacterLattice
    (Gm (Spec (CommRingCat.of k)))) (σ.coordinateLineRationalCharacter j hline))

/-- The algebraic line character gives its integer power action on every algebra. -/
theorem hasCoordinatePowerAction_coordinateLineCocharacterWeight
    (σ : MatrixRepresentation (Gm (Spec (CommRingCat.of k))).toGrp n)
    (j : n) (hline : σ.PreservesCoordinateLine j) :
    σ.HasCoordinatePowerAction j (σ.coordinateLineCocharacterWeight j hline) := by
  intro A _ _ x
  let ψ := σ.coordinateLineRationalCharacter j hline
  let lam : characterLattice (Gm (Spec (CommRingCat.of k))) :=
    (rationalCharacters.equivCharacterLattice _ ) ψ
  have hlam : lam = (gmEndEquiv k).symm (σ.coordinateLineCocharacterWeight j hline) :=
    ((gmEndEquiv k).symm_apply_apply lam).symm
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := isSplitTorus_gm.isAffineHom
  have h := characterSpace_affine (coordinateLine_mem_characterSpace σ j hline)
    (CommAlgCat.of k A) x
  have hvec : (fun r => algebraMap k A ((Pi.single j 1 : n → k) r)) =
      (Pi.single j 1 : n → A) := by
    ext r
    by_cases hr : r = j <;> simp [hr]
  rw [hvec] at h
  change (σ.affineMatrix (CommAlgCat.of k A) x : Matrix n n A) *ᵥ Pi.single j 1 =
    ((Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k A)
      (x ≫ ψ.toMul.hom.hom)) : A) •
        (Pi.single j 1 : n → A) at h
  rw [show ψ.toMul = CommGroupScheme.groupHom lam from rfl, hlam,
    gmEndEquiv_symm_comp, map_zpow] at h
  exact h

open GeneralLinear.CocharacterDiagonal

/-- A coordinate Gm eigenline becomes a prescribed universal exponent vector
after transport to the one-dimensional split torus. -/
theorem isExponentVector_of_coordinatePowerAction
    (σ : MatrixRepresentation (Gm (Spec (CommRingCat.of k))).toGrp n)
    (j : n) (m : ℤ) (hm : σ.HasCoordinatePowerAction j m) :
    IsExponentVector PUnit ((splitTorus.gmIso (Spec (CommRingCat.of k))).inv ≫ σ)
      (fun _ => m) (Pi.single j 1) := by
  intro A _ _ t
  let Z := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))
  let y : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) PUnit).X :=
    (splitTorus.algebraPointsEquiv PUnit A).symm t
  let x : Z ⟶ (Gm (Spec (CommRingCat.of k))).X :=
    y ≫ (splitTorus.gmIso (Spec (CommRingCat.of k))).inv.hom.hom
  have hxy : x ≫ (splitTorus.gmIso (Spec (CommRingCat.of k))).hom.hom.hom = y := by
    simp only [x, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  have ht := GeneralLinear.CocharacterDiagonal.algebraPointsEquiv_comp_gmIso x
  rw [hxy, show splitTorus.algebraPointsEquiv PUnit A y = t from
    MulEquiv.apply_symm_apply _ _] at ht
  have hu : t PUnit.unit =
      Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k A) x :=
    congrFun ht PUnit.unit
  have h := hm A x
  have hmat : matrixAt PUnit
      ((splitTorus.gmIso (Spec (CommRingCat.of k))).inv ≫ σ) t =
      σ.affineMatrix (CommAlgCat.of k A) x := by
    simp only [matrixAt]
    rfl
  have hvec : (fun r => algebraMap k A ((Pi.single j 1 : n → k) r)) =
      (Pi.single j 1 : n → A) := by
    ext r
    by_cases hr : r = j <;> simp [hr]
  rw [hmat, hvec]
  simpa [splitTorus.exponentValue, hu] using h

/-- One rational change of coordinates diagonalizes a cocharacter while retaining
the original eigenline and the integer of its actual line character. -/
theorem exists_diagonalization_retaining_coordinateLine
    (σ : MatrixRepresentation (Gm (Spec (CommRingCat.of k))).toGrp n)
    (j : n) (hline : σ.PreservesCoordinateLine j) :
    ∃ (B : GL n k) (e : n → ℤ) (a : n),
      (B : Matrix n n k).col a = Pi.single j 1 ∧
      e a = σ.coordinateLineCocharacterWeight j hline ∧
      σ ≫ ((GeneralLinear.groupScheme n (CommRingCat.of k)).innerIso
        (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)).hom =
          GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e := by
  classical
  let R := CommRingCat.of k
  let ρ : MatrixRepresentation (splitTorus (Spec R) PUnit) n :=
    (splitTorus.gmIso (Spec R)).inv ≫ σ
  have hρ : (splitTorus.gmIso (Spec R)).hom ≫ ρ = σ := by
    dsimp only [ρ]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let m := σ.coordinateLineCocharacterWeight j hline
  have hv : (Pi.single j (1 : k) : n → k) ≠ 0 := by
    intro h
    have h' := congrFun h j
    simp at h'
  have hweight := isExponentVector_of_coordinatePowerAction σ j m
    (σ.hasCoordinatePowerAction_coordinateLineCocharacterWeight j hline)
  obtain ⟨B, w, a, hB, hwa, hw⟩ :=
    exists_diagonalizingMatrix_containing PUnit ρ (fun _ => m) (Pi.single j 1) hv hweight
  refine ⟨B, fun b => w b PUnit.unit, a, hB, congrFun hwa PUnit.unit, ?_⟩
  apply Gm.hom_ext_universalPoint R
  let A : CommAlgCat R := CommAlgCat.of R (LaurentPolynomial k)
  let x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X := Gm.universalPoint R
  let t := splitTorus.algebraPointsEquiv PUnit (LaurentPolynomial k)
    (x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom)
  have hm : matrixAt PUnit ρ t =
      GeneralLinear.affinePointsEquiv n R A (x ≫ σ.hom.hom) := by
    dsimp only [matrixAt, t]
    rw [MulEquiv.symm_apply_apply, affineMatrix_apply, Category.assoc]
    change GeneralLinear.affinePointsEquiv n R A
      (x ≫ ((splitTorus.gmIso (Spec R)).hom ≫ ρ).hom.hom) = _
    rw [hρ]
  have ht : t = fun _ => Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x :=
    GeneralLinear.CocharacterDiagonal.algebraPointsEquiv_comp_gmIso x
  apply (GeneralLinear.affinePointsEquiv n R A).injective
  change GeneralLinear.affinePointsEquiv n R A
      ((x ≫ σ.hom.hom) ≫ ((GeneralLinear.groupScheme n R).innerIso
        (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)).hom.hom.hom) = _
  rw [comp_innerIso_hom, map_mul, map_mul, map_inv,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_constant_rationalMatrixPoint,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  simp only [map_inv, inv_inv]
  have h := hw (LaurentPolynomial k) t
  rw [hm, ht] at h
  simpa [A, x, R, splitTorus.exponentValue, diagonalMatrix,
    GeneralLinear.diagonalUnits, MonoidHom.pi] using h

end Langlands.GroupScheme.MatrixRepresentation
