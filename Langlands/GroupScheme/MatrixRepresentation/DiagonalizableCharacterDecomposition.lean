import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Torus.DiagonalizableAveraging
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof

/-! # Character decomposition for arbitrary diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation

namespace DiagonalizableCoefficients

open Diagonalizable.Averaging

variable {R : CommRingCat.{u}} (Λ : Type u) [AddCommGroup Λ]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (Diagonalizable.groupScheme R Λ).toGrp n)

/-- The matrix at the universal point of `D(Λ)`. -/
def universalMatrix : GL n (AddMonoidAlgebra R Λ) :=
  ρ.affineMatrix _ (universalPoint R Λ)

/-- The column of coefficients at a fixed character of `D(Λ)`. -/
def coefficientColumn (m : Λ) (j : n) : n → R :=
  fun i => ((universalMatrix Λ ρ : Matrix n n (AddMonoidAlgebra R Λ)) i j).coeff m

variable {A : Type u} [CommRing A] [Algebra R A]

private theorem affineMatrix_map {B : Type u} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (x : Lie.AffinePoints (Diagonalizable.groupScheme R Λ).toGrp A) :
    ρ.affineMatrix _ (Lie.affineMap _ f x) =
      Matrix.GeneralLinearGroup.map f.toRingHom (ρ.affineMatrix _ x) :=
  ρ.affineMatrix_naturality (CommAlgCat.ofHom f) x

/-- Translation of the universal matrix is multiplication by the point's matrix. -/
theorem universalMatrix_translated
    (x : Lie.AffinePoints (Diagonalizable.groupScheme R Λ).toGrp A) :
    Matrix.GeneralLinearGroup.map
        (((translation Λ (pointsEquiv R Λ A x)).restrictScalars R).comp
          (scalars R Λ A)).toRingHom (universalMatrix Λ ρ) =
      Matrix.GeneralLinearGroup.map (algebraMap A (AddMonoidAlgebra A Λ))
          (ρ.affineMatrix _ x) *
        Matrix.GeneralLinearGroup.map (scalars R Λ A).toRingHom (universalMatrix Λ ρ) := by
  rw [universalMatrix, ← affineMatrix_map, Lie.affineMap_comp, translation_point,
    map_mul, affineMatrix_map, affineMatrix_map]
  rfl

private theorem coeff_constant_mul (a : A) (p : AddMonoidAlgebra A Λ) (m : Λ) :
    (algebraMap A (AddMonoidAlgebra A Λ) a * p).coeff m = a * p.coeff m :=
  AddMonoidAlgebra.coeff_single_zero_mul p a m

omit [AddCommGroup Λ] [DecidableEq n] in
private theorem coeff_sum_univ (f : n → AddMonoidAlgebra A Λ) (m : Λ) :
    (∑ b, f b).coeff m = ∑ b, (f b).coeff m := by
  change (AddMonoidAlgebra.coeffAddEquiv (∑ b, f b)) m = _
  simp only [map_sum, AddMonoidAlgebra.coeffAddEquiv_apply]
  exact Finsupp.finsetSum_apply _ _ _

/-- Every coefficient column satisfies its character equation over every test algebra. -/
theorem coefficientColumn_weight
    (x : Lie.AffinePoints (Diagonalizable.groupScheme R Λ).toGrp A)
    (m : Λ) (j : n) :
    (ρ.affineMatrix _ x : Matrix n n A) *ᵥ
        (fun a => algebraMap R A (coefficientColumn Λ ρ m j a)) =
      (pointsEquiv R Λ A x (.ofAdd m) : A) •
        (fun a => algebraMap R A (coefficientColumn Λ ρ m j a)) := by
  funext a
  have h := congrArg
    (fun M : GL n (AddMonoidAlgebra A Λ) => (M.val a j).coeff m)
    (universalMatrix_translated Λ ρ x)
  change (translation Λ (pointsEquiv R Λ A x)
      ((scalars R Λ A)
        ((universalMatrix Λ ρ : Matrix n n (AddMonoidAlgebra R Λ)) a j))).coeff m =
    (∑ b, algebraMap A (AddMonoidAlgebra A Λ) ((ρ.affineMatrix _ x : Matrix n n A) a b) *
      (scalars R Λ A)
        ((universalMatrix Λ ρ : Matrix n n (AddMonoidAlgebra R Λ)) b j)).coeff m at h
  simp only [coeff_sum_univ, coeff_constant_mul, coeff_translation,
    scalars, AddMonoidAlgebra.coeff_mapAlgHom] at h
  exact h.symm.trans (mul_comm _ _)

/-- Evaluation at the trivial character is the identity matrix. -/
theorem universalMatrix_evaluateOne :
    Matrix.GeneralLinearGroup.map
        (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom.toRingHom
        (universalMatrix Λ ρ) = 1 := by
  rw [universalMatrix, ← affineMatrix_map]
  have hx : Lie.affineMap (Diagonalizable.groupScheme R Λ).toGrp
      (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom
      (universalPoint R Λ) = 1 := by
    apply (pointsEquiv R Λ R).injective
    rw [pointsEquiv_naturality, pointsEquiv_universalPoint, map_one]
    apply MonoidHom.ext
    intro m
    apply Units.ext
    change (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom
      (AddMonoidAlgebra.single m.toAdd 1) = 1
    simp
  rw [hx, map_one]

private theorem evaluateOne_eq_sum (p : AddMonoidAlgebra R Λ) :
    (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom p =
      ∑ m ∈ p.coeff.support, p.coeff m := by
  simp [Diagonalizable.lift, AddMonoidAlgebra.lift_apply', Finsupp.sum]

/-- The coefficient columns span the original finite free module. -/
theorem span_coefficientColumn :
    Submodule.span R (Set.range (fun q : Λ × n => coefficientColumn Λ ρ q.1 q.2)) = ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun R n).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  let U : Matrix n n (AddMonoidAlgebra R Λ) := universalMatrix Λ ρ
  let s : Finset Λ := Finset.univ.biUnion (fun a : n => (U a j).coeff.support)
  have hsum : ∑ m ∈ s, coefficientColumn Λ ρ m j = Pi.basisFun R n j := by
    funext a
    have h := congrArg (fun M : GL n R => (M : Matrix n n R) a j)
      (universalMatrix_evaluateOne Λ ρ)
    change (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom (U a j) =
      (1 : Matrix n n R) a j at h
    rw [evaluateOne_eq_sum] at h
    simp only [Finset.sum_apply, coefficientColumn]
    change ∑ m ∈ s, (U a j).coeff m = (Pi.basisFun R n j) a
    have hs : (U a j).coeff.support ⊆ s := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hm⟩
    calc
      ∑ m ∈ s, (U a j).coeff m = ∑ m ∈ (U a j).coeff.support, (U a j).coeff m := by
        symm
        apply Finset.sum_subset hs
        intro m _ hm
        exact Finsupp.notMem_support_iff.mp hm
      _ = (Pi.basisFun R n j) a := by
        simpa only [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm] using h
  rw [← hsum]
  exact Submodule.sum_mem _ (fun m _ =>
    Submodule.subset_span (Set.mem_range_self (m, j)))

/-- The existing evaluation character has the expected value on affine points. -/
theorem affineUnitsEquiv_evalCharacter (m : Λ)
    (x : Lie.AffinePoints (Diagonalizable.groupScheme R Λ).toGrp A) :
    Gm.affineUnitsEquiv R (CommAlgCat.of R A)
        (x ≫ (CommGroupScheme.groupHom
          (DiagonalizableCharacter.evalCharacter R Λ m)).hom.hom) =
      pointsEquiv R Λ A x (.ofAdd m) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (Gm.pointsEquiv _ _ (x ≫ (CommGroupScheme.groupHom
        (DiagonalizableCharacter.evalCharacter R Λ m)).hom.hom) :
          Γ(((algSpec R).obj (op (CommAlgCat.of R A))).left, ⊤)) = _
  rw [DiagonalizableCharacter.evalCharacter_apply]
  have h := Corepresented.map_affineSectionsIso_pointsEquiv (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) (CommAlgCat.of R A) x
  have hm := congrArg (fun r : Multiplicative Λ →* Aˣ => (r (.ofAdd m) : A)) h
  change (Corepresented.affineSectionsIso (CommAlgCat.of R A)).hom.hom
      (Diagonalizable.characterPointsEquiv R Λ _ x (.ofAdd m) :
        Γ(((algSpec R).obj (op (CommAlgCat.of R A))).left, ⊤)) = _ at hm
  change (Corepresented.affineSectionsIso (CommAlgCat.of R A)).hom.hom.toRingHom _ = _ at hm
  rw [Corepresented.affineSectionsIso_hom_ringHom] at hm
  exact hm

end DiagonalizableCoefficients

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (Λ : Type u) [AddCommGroup Λ]

/-- A coefficient column belongs to the character space of its exponent. -/
theorem diagonalizable_coefficientColumn_mem_characterSpace
    (ρ : MatrixRepresentation (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp n)
    (m : Λ) (j : n) :
    DiagonalizableCoefficients.coefficientColumn Λ ρ m j ∈
      ρ.characterSpace ((rationalCharacters.equivCharacterLattice
        (Diagonalizable.groupScheme (CommRingCat.of k) Λ)).symm
          (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m)) := by
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  change (ρ.affineMatrix A x : Matrix n n A) *ᵥ
      (fun r => algebraMap k A (DiagonalizableCoefficients.coefficientColumn Λ ρ m j r)) =
    (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) A)
      (x ≫ (CommGroupScheme.groupHom
        (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m)).hom.hom) : A) •
      (fun r => algebraMap k A (DiagonalizableCoefficients.coefficientColumn Λ ρ m j r))
  rw [DiagonalizableCoefficients.affineUnitsEquiv_evalCharacter]
  exact DiagonalizableCoefficients.coefficientColumn_weight Λ ρ x m j

/-- Character spaces span a representation of `D(Λ)`, including torsion in `Λ`. -/
theorem iSup_characterSpace_eq_top_diagonalizable
    (ρ : MatrixRepresentation (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp n) :
    (⨆ χ : rationalCharacters (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp,
      ρ.characterSpace χ) = ⊤ := by
  apply top_unique
  rw [← DiagonalizableCoefficients.span_coefficientColumn Λ ρ]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨m, j⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem _
    (diagonalizable_coefficientColumn_mem_characterSpace Λ ρ m j)

/-- Transport of character-space spanning along a supplied diagonalizable isomorphism. -/
theorem iSup_characterSpace_eq_top_of_diagonalizable_iso
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (e : G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (ρ : MatrixRepresentation G n) :
    (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤ := by
  apply top_unique
  rw [← iSup_characterSpace_eq_top_diagonalizable Λ (ρ.restrict e.inv)]
  apply iSup_le
  intro χ
  rw [characterSpace_restrict_iso]
  exact le_iSup _ _

/-- The character spaces of a diagonalizable representation form an internal direct sum. -/
theorem isInternal_characterSpace_of_diagonalizable_iso
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (e : G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (ρ : MatrixRepresentation G n) :
    DirectSum.IsInternal ρ.characterSpace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (characterSpace_iSupIndep ρ) (iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e ρ)

end Langlands.GroupScheme.MatrixRepresentation
