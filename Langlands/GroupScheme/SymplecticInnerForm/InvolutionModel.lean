import Langlands.GroupScheme.Quaternionic.IsometryCut
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.FieldTheory.Galois.Basic

/-! # Symplectic splitting charts and norm-one isometry groups of involutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SymplecticInnerForm

open Quaternionic

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]

/-- A finite Galois chart carrying an involution to the adjoint involution of the
standard alternating matrix. The multiplication identity also applies in characteristic two. -/
def HasStandardSymplecticSplitting (τ : FirstKindInvolution K A) (n : ℕ) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
    (_ : FiniteDimensional K L) (_ : IsGalois K L),
    ∃ e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L,
      ∀ x, e (τ.baseChange L x) * Matrix.J (Fin n) L =
        Matrix.J (Fin n) L * (e x).transpose

variable [FiniteDimensional K A] (τ : FirstKindInvolution K A)

/-- The group scheme whose tensor units satisfy `u τ(u) = 1`. -/
abbrev isometryGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  IsometryCut.groupScheme (τ := τ) (M := ⊥) IsometryCut.isStable_bot (1 : A)

/-- The inclusion of the involution isometries into the algebra-unit group. -/
def isometryι : isometryGroup τ ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K A) :=
  IsometryCut.inclusion IsometryCut.isStable_bot (1 : A)

theorem isClosedSubgroup_isometryι : IsClosedSubgroup (isometryι τ) :=
  IsometryCut.isClosedSubgroup_inclusion IsometryCut.isStable_bot (1 : A)

instance mono_isometryι : Mono (isometryι τ).hom.hom := by
  have : IsClosedImmersion (isometryι τ).hom.hom.left := isClosedSubgroup_isometryι τ
  exact Over.mono_of_mono_left _

/-- On any relative test scheme, membership is the involution-isometry equation
over its algebra of global sections. -/
theorem mem_range_isometryι_iff {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K A)).X) :
    x ∈ (SubgroupFunctor.range (isometryι τ)).carrier T ↔
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T x :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] A) *
        τ.baseChange ((algΓ (CommRingCat.of K)).obj T).unop
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T x) = 1 := by
  rw [isometryι, IsometryCut.mem_range_inclusion_iff, Submodule.baseChange_bot,
    Submodule.mem_bot, IsometryCut.defect, sub_eq_zero]
  rw [← Algebra.TensorProduct.one_def, mul_one]

variable [Algebra.IsCentral K A] [IsSimpleRing A]

/-- The reduced-norm-one subgroup of the involution isometries. -/
def normOneGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  kernel (isometryι τ ≫ CentralSimpleUnits.reducedNormHom K A)

/-- The kernel inclusion into the involution-isometry group. -/
def normOneGroupι : normOneGroup τ ⟶ isometryGroup τ :=
  kernelι _

/-- The inclusion of the norm-one involution isometries into the algebra-unit group. -/
def normOneAmbientι : normOneGroup τ ⟶ CentralSimpleUnits.groupScheme K A :=
  normOneGroupι τ ≫ isometryι τ

instance mono_normOneAmbientι : Mono (normOneAmbientι τ).hom.hom := by
  have : Mono (normOneGroupι τ).hom.hom := kernelι_mono _
  rw [normOneAmbientι, Grp.comp_hom_hom]
  infer_instance

/-- The ambient inclusion represents its range on all test schemes. -/
theorem isRepresentedBy_normOneAmbientι :
    (SubgroupFunctor.range (normOneAmbientι τ)).IsRepresentedBy (normOneAmbientι τ) :=
  ⟨inferInstance, rfl⟩

/-- An involution isometry lies in the kernel precisely when its reduced norm is one. -/
theorem mem_range_normOneGroupι_iff {T : Over (Spec (CommRingCat.of K))}
    (y : T ⟶ (isometryGroup τ).X) :
    y ∈ (SubgroupFunctor.range (normOneGroupι τ)).carrier T ↔
      y ≫ (isometryι τ).hom.hom ≫
        (CentralSimpleUnits.reducedNormHom K A).hom.hom = 1 := by
  have h := mem_range_kernelι_iff
    (isometryι τ ≫ CentralSimpleUnits.reducedNormHom K A) y
  rw [Grp.comp_hom_hom] at h
  exact h

/-- On every relative test, the ambient range consists of the involution isometries
whose reduced norm is one. -/
theorem mem_range_normOneAmbientι_iff {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (CentralSimpleUnits.groupScheme K A).X) :
    x ∈ (SubgroupFunctor.range (normOneAmbientι τ)).carrier T ↔
      x ∈ (SubgroupFunctor.range (isometryι τ)).carrier T ∧
        x ≫ (CentralSimpleUnits.reducedNormHom K A).hom.hom = 1 := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range, normOneAmbientι,
    Grp.comp_hom_hom]
  constructor
  · rintro ⟨y, rfl⟩
    have hk := (mem_range_normOneGroupι_iff τ (y ≫ (normOneGroupι τ).hom.hom)).1
      (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    refine ⟨⟨y ≫ (normOneGroupι τ).hom.hom, Category.assoc _ _ _⟩, ?_⟩
    simpa only [Category.assoc] using hk
  · rintro ⟨⟨y, rfl⟩, hN⟩
    have hk := (mem_range_normOneGroupι_iff τ y).2 (by
      rw [← Category.assoc]
      exact hN)
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hk
    exact ⟨z, (Category.assoc _ _ _).symm⟩

end Langlands.GroupScheme.SymplecticInnerForm
