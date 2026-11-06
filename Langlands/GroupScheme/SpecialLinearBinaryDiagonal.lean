import Langlands.GroupScheme.SpecialLinearBinaryBigCell
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # The actual diagonal intersection in the binary special linear group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

section Matrices

variable {A : Type u} [CommRing A]

/-- The determinant-one diagonal matrix with prescribed last diagonal unit. -/
def diagonalMatrix (t : Aˣ) : Matrix.SpecialLinearGroup (Fin 2) A :=
  ⟨!![(↑t⁻¹ : A), 0; 0, (↑t : A)], by simp [Matrix.det_fin_two]⟩

/-- Diagonal matrices form a homomorphism from the units of the original ring. -/
def diagonalMatrixHom : Aˣ →* Matrix.SpecialLinearGroup (Fin 2) A where
  toFun := diagonalMatrix
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagonalMatrix]
  map_mul' t s := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Vanishing of both off-diagonal entries identifies the matrix with its diagonal unit. -/
theorem diagonalMatrix_diagonalUnit (a : subgroup A) (ha : a.val 0 1 = 0) :
    diagonalMatrix (diagonalUnit a) = a.val := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hb : a.val 1 0 = 0 := a.property
  fin_cases i <;> fin_cases j <;> simp [diagonalMatrix, diagonalUnit, ha, hb]

end Matrices

section Schemes

variable (R : CommRingCat.{u})

/-- A rank-one character lattice in the universe of the base ring. -/
abbrev DiagonalLattice : Type u := PUnit.{u + 1} → ℤ

/-- Points of this actual diagonalizable group are single global units. -/
def diagonalTorusPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (Diagonalizable.groupScheme R DiagonalLattice).X) ≃* (Γ(T.left, ⊤))ˣ :=
  (Diagonalizable.splitPointsEquiv R (AddEquiv.refl DiagonalLattice) T).trans
    (MulEquiv.piUnique fun _ : PUnit.{u + 1} => (Γ(T.left, ⊤))ˣ)

theorem diagonalTorusPointsEquiv_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (Diagonalizable.groupScheme R DiagonalLattice).X) :
    diagonalTorusPointsEquiv R T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (diagonalTorusPointsEquiv R T x) := by
  change Diagonalizable.splitPointsEquiv R (AddEquiv.refl DiagonalLattice) T'
    (a ≫ x) PUnit.unit = _
  rw [Diagonalizable.splitPointsEquiv_naturality]
  rfl

/-- The pointwise diagonal homomorphism from an actual diagonalizable group. -/
def diagonalInclusionPoints (T : Over (Spec R)) :
    (T ⟶ (Diagonalizable.groupScheme R DiagonalLattice).X) →*
      (T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :=
  (SpecialLinear.pointsEquiv (Fin 2) R T).symm.toMonoidHom.comp
    (diagonalMatrixHom.comp (diagonalTorusPointsEquiv R T).toMonoidHom)

theorem diagonalInclusionPoints_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (Diagonalizable.groupScheme R DiagonalLattice).X) :
    diagonalInclusionPoints R T' (a ≫ x) = a ≫ diagonalInclusionPoints R T x := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R T').injective
  simp only [diagonalInclusionPoints, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply, SpecialLinear.pointsEquiv_naturality,
    diagonalTorusPointsEquiv_naturality]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonalMatrixHom, diagonalMatrix]

/-- The actual rank-one diagonalizable homomorphism into the binary special linear group. -/
def diagonalInclusion :
    (Diagonalizable.groupScheme R DiagonalLattice).toGrp ⟶
      SpecialLinear.groupScheme (Fin 2) R :=
  homOfPoints (diagonalInclusionPoints R) (diagonalInclusionPoints_naturality R)

/-- The actual homomorphism is the prescribed diagonal matrix on every test scheme. -/
theorem pointsEquiv_diagonalInclusion (T : Over (Spec R))
    (x : T ⟶ (Diagonalizable.groupScheme R DiagonalLattice).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (x ≫ (diagonalInclusion R).hom.hom) =
      diagonalMatrix (diagonalTorusPointsEquiv R T x) := by
  rw [diagonalInclusion, comp_homOfPoints]
  exact (SpecialLinear.pointsEquiv (Fin 2) R T).apply_symm_apply _

/-- Every common upper and Weyl-conjugate upper point comes from the same diagonalizable
group, globally on the original relative test scheme. -/
theorem exists_diagonal_lift_of_eq_conjugate (T : Over (Spec R))
    (c c' : T ⟶ (groupScheme R).X)
    (h : c ≫ (inclusion R).hom.hom = c' ≫ (conjugateInclusion R).hom.hom) :
    ∃ t : T ⟶ (Diagonalizable.groupScheme R DiagonalLattice).toGrp.X,
      c ≫ (inclusion R).hom.hom = t ≫ (diagonalInclusion R).hom.hom := by
  have hm := congrArg (SpecialLinear.pointsEquiv (Fin 2) R T) h
  rw [pointsEquiv_inclusion, pointsEquiv_conjugateInclusion] at hm
  have ha := upperEntry_eq_zero_of_eq_conjugate _ _ hm
  refine ⟨(diagonalTorusPointsEquiv R T).symm
    (diagonalUnit (pointsEquiv R T c)), ?_⟩
  apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
  rw [pointsEquiv_inclusion, pointsEquiv_diagonalInclusion, MulEquiv.apply_symm_apply]
  exact (diagonalMatrix_diagonalUnit _ ha).symm

/-- The two triangular ranges intersect in exactly the range of this actual
diagonalizable homomorphism, on every test scheme. -/
theorem mem_diagonalInclusion_range_iff {T : Over (Spec R)}
    (g : T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :
    g ∈ (SubgroupFunctor.range (diagonalInclusion R)).carrier T ↔
      g ∈ (SubgroupFunctor.range (inclusion R)).carrier T ∧
        g ∈ (SubgroupFunctor.range (conjugateInclusion R)).carrier T := by
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨t, rfl⟩
    rw [mem_range_inclusion, mem_range_conjugateInclusion,
      pointsEquiv_diagonalInclusion]
    simp [diagonalMatrix]
  · intro hg
    rw [SubgroupFunctor.mem_range] at hg
    obtain ⟨c, hc⟩ := hg.1
    have hg2 := hg.2
    rw [SubgroupFunctor.mem_range] at hg2
    obtain ⟨c', hc'⟩ := hg2
    obtain ⟨t, ht⟩ := exists_diagonal_lift_of_eq_conjugate R T c c' (hc.trans hc'.symm)
    rw [SubgroupFunctor.mem_range]
    exact ⟨t, ht.symm.trans hc⟩

end Schemes

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
