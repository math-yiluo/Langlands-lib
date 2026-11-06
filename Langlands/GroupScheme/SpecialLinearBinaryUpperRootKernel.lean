import Langlands.GroupScheme.SpecialLinearBinaryRootClosed
import Langlands.GroupScheme.SpecialLinearBinaryUpper
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # The actual additive kernel of the binary upper-triangular diagonal character -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

section Matrices

variable {A : Type u} [CommRing A]

/-- The upper transvection, with its actual upper-triangular subgroup codomain. -/
def upperTransvectionHom : Multiplicative A →* subgroup A :=
  (BinaryRoot.transvectionHom (show (0 : Fin 2) ≠ 1 by decide)).codRestrict _
    (fun a => by
      change (Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 2) ≠ 1 by decide) a.toAdd) 1 0 = 0
      simp [Matrix.SpecialLinearGroup.transvection_coe])

/-- The last diagonal unit of an upper transvection is one. -/
theorem diagonalHom_upperTransvectionHom (a : Multiplicative A) :
    diagonalHom (upperTransvectionHom a) = 1 := by
  apply Units.ext
  simp [diagonalHom, diagonalUnit, upperTransvectionHom,
    BinaryRoot.transvectionHom, Matrix.SpecialLinearGroup.transvection_coe]

/-- The kernel of the last diagonal consists exactly of upper transvections. -/
theorem mem_upperTransvection_range (g : subgroup A) :
    g ∈ (upperTransvectionHom (A := A)).range ↔ diagonalHom g = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact diagonalHom_upperTransvectionHom a
  · intro hg
    have h11 : g.val 1 1 = 1 := congrArg Units.val hg
    have h10 : g.val 1 0 = 0 := g.property
    have h00 : g.val 0 0 = 1 := by
      have hd := g.val.property
      rwa [Matrix.det_fin_two, h10, h11, mul_zero, sub_zero, mul_one] at hd
    refine ⟨Multiplicative.ofAdd (g.val 0 1), ?_⟩
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro r s
    fin_cases r <;> fin_cases s <;>
      simp [upperTransvectionHom, BinaryRoot.transvectionHom,
        Matrix.SpecialLinearGroup.transvection_coe, h00, h10, h11]

end Matrices

section Schemes

variable (R : CommRingCat.{u})

/-- The additive root points, now valued in the actual triangular group scheme. -/
def upperRootPoints (T : Over (Spec R)) :
    (T ⟶ (VectorGroup.groupScheme R 1).X) →* (T ⟶ (groupScheme R).X) :=
  (pointsEquiv R T).symm.toMonoidHom.comp
    (upperTransvectionHom.comp (BinaryRoot.coefficientEquiv R T).toMonoidHom)

theorem pointsEquiv_upperRootPoints (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    pointsEquiv R T (upperRootPoints R T x) =
      upperTransvectionHom (BinaryRoot.coefficientEquiv R T x) :=
  (pointsEquiv R T).apply_symm_apply _

theorem upperRootPoints_inclusion (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    upperRootPoints R T x ≫ (inclusion R).hom.hom =
      x ≫ (BinaryRoot.upperMap R).hom.hom := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
  rw [pointsEquiv_inclusion, pointsEquiv_upperRootPoints, BinaryRoot.pointsEquiv_rootMap]
  rfl

theorem upperRootPoints_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    upperRootPoints R T' (a ≫ x) = a ≫ upperRootPoints R T x := by
  apply (cancel_mono (inclusion R).hom.hom).mp
  simp only [Category.assoc, upperRootPoints_inclusion]

/-- The actual additive root inclusion into the actual triangular group. -/
def upperRootMap : VectorGroup.groupScheme R 1 ⟶ groupScheme R :=
  homOfPoints (upperRootPoints R) (upperRootPoints_naturality R)

theorem comp_upperRootMap (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    x ≫ (upperRootMap R).hom.hom = upperRootPoints R T x :=
  comp_homOfPoints _ _ T x

/-- Forgetting the triangular condition recovers the existing upper root map. -/
theorem upperRootMap_comp_inclusion :
    upperRootMap R ≫ inclusion R = BinaryRoot.upperMap R := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_upperRootMap, upperRootPoints_inclusion]

instance isClosedImmersion_upperRootMap :
    IsClosedImmersion (upperRootMap R).hom.hom.left := by
  have : IsClosedImmersion
      ((upperRootMap R).hom.hom.left ≫ (inclusion R).hom.hom.left) := by
    change IsClosedSubgroup (upperRootMap R ≫ inclusion R)
    rw [upperRootMap_comp_inclusion]
    exact BinaryRoot.isClosedSubgroup_rootMap R _
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (inclusion R).hom.hom.left

theorem isClosedSubgroup_upperRootMap : IsClosedSubgroup (upperRootMap R) :=
  isClosedImmersion_upperRootMap R

instance mono_upperRootMap : Mono (upperRootMap R).hom.hom := by
  have : SurjectiveOnStalks (upperRootMap R).hom.hom.left :=
    (isClosedImmersion_upperRootMap R).toSurjectiveOnStalks
  have : Mono (upperRootMap R).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective
      (isClosedImmersion_upperRootMap R).isClosedEmbedding.injective
  exact Over.mono_of_mono_left _

/-- On every test scheme, the upper root range is the kernel of the last diagonal unit. -/
theorem mem_range_upperRootMap_iff_diagonalPoints {T : Over (Spec R)}
    (g : T ⟶ (groupScheme R).X) :
    g ∈ (SubgroupFunctor.range (upperRootMap R)).carrier T ↔ diagonalPoints R T g = 1 := by
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    change diagonalHom (pointsEquiv R T (x ≫ (upperRootMap R).hom.hom)) = 1
    rw [comp_upperRootMap, pointsEquiv_upperRootPoints]
    exact diagonalHom_upperTransvectionHom _
  · intro hg
    obtain ⟨a, ha⟩ := (mem_upperTransvection_range (pointsEquiv R T g)).mpr hg
    refine ⟨(BinaryRoot.coefficientEquiv R T).symm a, ?_⟩
    apply (pointsEquiv R T).injective
    rw [comp_upperRootMap, pointsEquiv_upperRootPoints, MulEquiv.apply_symm_apply]
    exact ha

/-- This range is the full actual scheme-theoretic kernel range, on all tests. -/
theorem range_kernelι_diagonalMorphism :
    SubgroupFunctor.range (kernelι (diagonalMorphism R)) =
      SubgroupFunctor.range (upperRootMap R) := by
  ext T g
  rw [mem_range_kernelι_iff, mem_range_upperRootMap_iff_diagonalPoints]
  constructor
  · intro hg
    have h := congrArg (Gm.pointsEquiv (Spec R) T) hg
    rw [comp_diagonalMorphism, (Gm.pointsEquiv (Spec R) T).map_one] at h
    simpa only [diagonalPointToGm, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulEquiv.apply_symm_apply] using h
  · intro hg
    apply (Gm.pointsEquiv (Spec R) T).injective
    rw [comp_diagonalMorphism, (Gm.pointsEquiv (Spec R) T).map_one]
    simpa only [diagonalPointToGm, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulEquiv.apply_symm_apply] using hg

/-- The full kernel group scheme of the diagonal character is the actual additive group. -/
def diagonalKernelIso : kernel (diagonalMorphism R) ≅ VectorGroup.groupScheme R 1 :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range (kernelι (diagonalMorphism R))) ⟨inferInstance, rfl⟩
    ⟨inferInstance, (range_kernelι_diagonalMorphism R).symm⟩

/-- The kernel isomorphism preserves the actual inclusions into the triangular group. -/
theorem diagonalKernelIso_hom_comp :
    (diagonalKernelIso R).hom ≫ upperRootMap R = kernelι (diagonalMorphism R) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (F := SubgroupFunctor.range (kernelι (diagonalMorphism R))) ⟨inferInstance, rfl⟩
    ⟨inferInstance, (range_kernelι_diagonalMorphism R).symm⟩

/-- The upper additive root subgroup is normal in the triangular group on every test. -/
theorem isNormal_range_upperRootMap : (SubgroupFunctor.range (upperRootMap R)).IsNormal := by
  intro T g x _ hx
  rw [← range_kernelι_diagonalMorphism, mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

end Schemes

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
