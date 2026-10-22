import Langlands.Cohomology.CokernelComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.Additive

/-!
# Transporting the cokernel construction along a right exact functor

Let `Φ : A ⥤ B` preserve cokernels, and let `e : T ⋙ Φ ≅ Φ ⋙ T'` intertwine
two coaugmented endofunctors `η : 𝟭 A ⟶ T` and `η' : 𝟭 B ⟶ T'`. Then `Φ`
carries the iterated-cokernel complex of `(T, η)` to that of `(T', η')`,
naturally and compatibly with the augmentations.
-/

noncomputable section

namespace Langlands.Cohomology.CokernelComplex

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable {T : A ⥤ A} {η : 𝟭 A ⟶ T} {T' : B ⥤ B} {η' : 𝟭 B ⟶ T'}
variable {Φ : A ⥤ B} [Φ.PreservesZeroMorphisms]
variable [PreservesColimitsOfShape WalkingParallelPair Φ]
variable (e : T ⋙ Φ ≅ Φ ⋙ T')
variable (he : ∀ M : A, Φ.map (η.app M) ≫ e.hom.app M = η'.app (Φ.obj M))

omit [Abelian B] [PreservesColimitsOfShape WalkingParallelPair Φ] in
/-- Postcomposition with `Φ` preserves zero natural transformations. -/
instance whiskeringRight_preservesZeroMorphisms :
    ((Functor.whiskeringRight A A B).obj Φ).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext M
    exact Φ.map_zero _ _

omit [Abelian A] [Φ.PreservesZeroMorphisms]
  [PreservesColimitsOfShape WalkingParallelPair Φ] in
/-- Precomposition with `Φ` preserves zero natural transformations. -/
instance whiskeringLeft_preservesZeroMorphisms :
    ((Functor.whiskeringLeft A B B).obj Φ).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- A comparison of residual functors induces a comparison of the terms. -/
def termIsoOf {R : A ⥤ A} {R' : B ⥤ B} (ρ : R ⋙ Φ ≅ Φ ⋙ R') :
    (R ⋙ T) ⋙ Φ ≅ Φ ⋙ (R' ⋙ T') :=
  Functor.isoWhiskerLeft R e ≪≫ Functor.isoWhiskerRight ρ T'

omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms]
  [PreservesColimitsOfShape WalkingParallelPair Φ] in
@[simp]
theorem termIsoOf_hom_app {R : A ⥤ A} {R' : B ⥤ B} (ρ : R ⋙ Φ ≅ Φ ⋙ R') (M : A) :
    (termIsoOf e ρ).hom.app M = e.hom.app (R.obj M) ≫ T'.map (ρ.hom.app M) :=
  rfl

omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms]
  [PreservesColimitsOfShape WalkingParallelPair Φ] in
include he in
/-- The term comparison intertwines the two coaugmentations. -/
theorem termIsoOf_comm {R : A ⥤ A} {R' : B ⥤ B} (ρ : R ⋙ Φ ≅ Φ ⋙ R') (M : A) :
    Φ.map (η.app (R.obj M)) ≫ (termIsoOf e ρ).hom.app M =
      ρ.hom.app M ≫ η'.app (R'.obj (Φ.obj M)) := by
  rw [termIsoOf_hom_app, ← Category.assoc, he]
  exact (η'.naturality (ρ.hom.app M)).symm

omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms]
  [PreservesColimitsOfShape WalkingParallelPair Φ] in
include he in
/-- The same compatibility as an equation of natural transformations. -/
theorem termIsoOf_comm_nat {R : A ⥤ A} {R' : B ⥤ B} (ρ : R ⋙ Φ ≅ Φ ⋙ R') :
    Functor.whiskerRight (Functor.whiskerLeft R η) Φ ≫ (termIsoOf e ρ).hom =
      ρ.hom ≫ Functor.whiskerLeft Φ (Functor.whiskerLeft R' η') := by
  ext M
  exact termIsoOf_comm e he ρ M

/-- One cokernel step of the comparison. -/
def stepIso {R : A ⥤ A} {R' : B ⥤ B} (ρ : R ⋙ Φ ≅ Φ ⋙ R') :
    cokernel (Functor.whiskerLeft R η) ⋙ Φ ≅ Φ ⋙ cokernel (Functor.whiskerLeft R' η') :=
  PreservesCokernel.iso ((Functor.whiskeringRight A A B).obj Φ) (Functor.whiskerLeft R η) ≪≫
    cokernel.mapIso _ (((Functor.whiskeringLeft A B B).obj Φ).map (Functor.whiskerLeft R' η'))
      ρ (termIsoOf e ρ) (termIsoOf_comm_nat e he ρ) ≪≫
    (PreservesCokernel.iso ((Functor.whiskeringLeft A B B).obj Φ)
      (Functor.whiskerLeft R' η')).symm

theorem stepIso_comm {R : A ⥤ A} {R' : B ⥤ B} (ρ : R ⋙ Φ ≅ Φ ⋙ R') :
    Functor.whiskerRight (cokernel.π (Functor.whiskerLeft R η)) Φ ≫ (stepIso e he ρ).hom =
      (termIsoOf e ρ).hom ≫ Functor.whiskerLeft Φ (cokernel.π (Functor.whiskerLeft R' η')) := by
  have h₁ := PreservesCokernel.π_iso_hom ((Functor.whiskeringRight A A B).obj Φ)
    (Functor.whiskerLeft R η)
  have h₂ := PreservesCokernel.π_iso_hom ((Functor.whiskeringLeft A B B).obj Φ)
    (Functor.whiskerLeft R' η')
  dsimp only [stepIso, Iso.trans_hom, Iso.symm_hom, cokernel.mapIso, cokernel.map]
  rw [← Category.assoc, ← Category.assoc]
  erw [h₁]
  rw [cokernel.π_desc, Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  rfl

/-- The comparison of the successive residual functors. -/
def residualIso : (n : ℕ) → residual T η n ⋙ Φ ≅ Φ ⋙ residual T' η' n
  | 0 => Functor.leftUnitor Φ ≪≫ (Functor.rightUnitor Φ).symm
  | n + 1 => stepIso e he (residualIso n)

/-- The comparison of the degree-`n` terms. -/
def termIso (n : ℕ) : term T η n ⋙ Φ ≅ Φ ⋙ term T' η' n :=
  termIsoOf e (residualIso e he n)

theorem inclusion_comm (n : ℕ) (M : A) :
    Φ.map ((inclusion T η n).app M) ≫ (termIso e he n).hom.app M =
      (residualIso e he n).hom.app M ≫ (inclusion T' η' n).app (Φ.obj M) :=
  termIsoOf_comm e he (residualIso e he n) M

theorem quotient_comm (n : ℕ) (M : A) :
    Φ.map ((quotient T η n).app M) ≫ (residualIso e he (n + 1)).hom.app M =
      (termIso e he n).hom.app M ≫ (quotient T' η' n).app (Φ.obj M) :=
  NatTrans.congr_app (stepIso_comm e he (residualIso e he n)) M

theorem differential_comm (n : ℕ) (M : A) :
    Φ.map ((differential T η n).app M) ≫ (termIso e he (n + 1)).hom.app M =
      (termIso e he n).hom.app M ≫ (differential T' η' n).app (Φ.obj M) := by
  simp only [differential, NatTrans.comp_app, Φ.map_comp, Category.assoc]
  rw [inclusion_comm, ← Category.assoc, quotient_comm, Category.assoc]

/-- The comparison of the complexes of one object. -/
def complexIso (M : A) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex T η M) ≅
      complex T' η' (Φ.obj M) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (termIso e he n).app M) (by
    rintro i j (rfl : i + 1 = j)
    simp only [Functor.mapHomologicalComplex_obj_d, complex_d, Iso.app_hom]
    exact (differential_comm e he i M).symm)

@[simp]
theorem complexIso_hom_f (M : A) (n : ℕ) :
    (complexIso e he M).hom.f n = (termIso e he n).hom.app M :=
  rfl

/-- `Φ` carries the cokernel complex of `(T, η)` to that of `(T', η')`. -/
def functorIso :
    functor T η ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℕ) ≅ Φ ⋙ functor T' η' :=
  NatIso.ofComponents (complexIso e he) (fun {M N} f => by
    ext n
    exact (termIso e he n).hom.naturality f)

@[simp]
theorem functorIso_hom_app_f (M : A) (n : ℕ) :
    ((functorIso e he).hom.app M).f n = (termIso e he n).hom.app M :=
  rfl

/-- The comparison is compatible with the augmentations. -/
theorem map_augmentation_functorIso (M : A) :
    Φ.map (augmentation T η M) ≫ ((functorIso e he).hom.app M).f 0 =
      augmentation T' η' (Φ.obj M) := by
  rw [functorIso_hom_app_f]
  change Φ.map (η.app M) ≫ e.hom.app M ≫ T'.map (𝟙 (Φ.obj M) ≫ 𝟙 (Φ.obj M)) =
    η'.app (Φ.obj M)
  rw [Category.comp_id, T'.map_id]
  erw [Category.comp_id]
  exact he M

end Langlands.Cohomology.CokernelComplex
