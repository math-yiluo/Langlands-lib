import Langlands.Cohomology.CokernelComplex.LaxMap
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Change of the functor in the actual lax cokernel-complex comparison -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.CokernelComplex.Lax

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

variable {A : Type u} [Category.{v} A]
  {B : Type u'} [Category.{v'} B]
  {T : A ⥤ A} {η : 𝟭 A ⟶ T} {T' : B ⥤ B} {η' : 𝟭 B ⟶ T'}
  {Φ Ψ : A ⥤ B}
  (e : Φ ⋙ T' ⟶ T ⋙ Φ) (e' : Ψ ⋙ T' ⟶ T ⋙ Ψ)
  (α : Φ ⟶ Ψ)
  (hα : ∀ M : A, T'.map (α.app M) ≫ e'.app M = e.app M ≫ α.app (T.obj M))

include hα in
/-- A compatible transformation of residual comparisons induces the same
square for their term comparisons. -/
theorem termMapOf_transformation {R : A ⥤ A} {R' : B ⥤ B}
    (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) (ρ' : Ψ ⋙ R' ⟶ R ⋙ Ψ)
    (hρ : ∀ M : A, R'.map (α.app M) ≫ ρ'.app M = ρ.app M ≫ α.app (R.obj M))
    (M : A) :
    (R' ⋙ T').map (α.app M) ≫ (termMapOf e' ρ').app M =
      (termMapOf e ρ).app M ≫ α.app ((R ⋙ T).obj M) := by
  change T'.map (R'.map (α.app M)) ≫ (T'.map (ρ'.app M) ≫ e'.app (R.obj M)) = _
  rw [← Functor.map_comp_assoc, hρ, Functor.map_comp, Category.assoc, hα]
  simp only [termMapOf_app, Functor.comp_obj, Category.assoc]

variable [Abelian A] [Abelian B]
  [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms]
  (he : ∀ M : A, η'.app (Φ.obj M) ≫ e.app M = Φ.map (η.app M))
  (he' : ∀ M : A, η'.app (Ψ.obj M) ≫ e'.app M = Ψ.map (η.app M))

include hα in
/-- Every actual residual comparison is compatible with a transformation
of the original functors, by uniqueness of cokernel descent. -/
theorem residualMap_transformation (n : ℕ) (M : A) :
    (residual T' η' n).map (α.app M) ≫ (residualMap e' he' n).app M =
      (residualMap e he n).app M ≫ α.app ((residual T η n).obj M) := by
  induction n generalizing M with
  | zero =>
    change α.app M ≫ 𝟙 (Ψ.obj M) = 𝟙 (Φ.obj M) ≫ α.app M
    rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
    have : Epi (quotient T' η' n) := by
      dsimp only [quotient]
      infer_instance
    have : Epi ((quotient T' η' n).app (Φ.obj M)) := by
      infer_instance
    apply (cancel_epi ((quotient T' η' n).app (Φ.obj M))).1
    rw [← Category.assoc, ← (quotient T' η' n).naturality (α.app M),
      Category.assoc, quotient_comm e' he']
    rw [← Category.assoc ((quotient T' η' n).app (Φ.obj M)),
      quotient_comm e he, Category.assoc]
    have ht := termMapOf_transformation e e' α hα
      (residualMap e he n) (residualMap e' he' n) ih M
    change (term T' η' n).map (α.app M) ≫ (termMap e' he' n).app M =
      (termMap e he n).app M ≫ α.app ((term T η n).obj M) at ht
    change (term T' η' n).map (α.app M) ≫
        ((termMap e' he' n).app M ≫ Ψ.map ((quotient T η n).app M)) =
      (termMap e he n).app M ≫
        (Φ.map ((quotient T η n).app M) ≫ α.app ((residual T η (n + 1)).obj M))
    rw [← Category.assoc, ht, Category.assoc, α.naturality]

include hα in
/-- The transformation square holds in every actual term of the complex. -/
theorem termMap_transformation (n : ℕ) (M : A) :
    (term T' η' n).map (α.app M) ≫ (termMap e' he' n).app M =
      (termMap e he n).app M ≫ α.app ((term T η n).obj M) :=
  termMapOf_transformation e e' α hα (residualMap e he n) (residualMap e' he' n)
    (residualMap_transformation e e' α hα he he' n) M

include hα in
/-- The square of genuine chain maps commutes for every compatible natural
transformation, without assuming it invertible. -/
theorem complexMap_transformation (M : A) :
    (functor T' η').map (α.app M) ≫ complexMap e' he' M =
      complexMap e he M ≫
        (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app (complex T η M) := by
  ext n
  exact termMap_transformation e e' α hα he he' n M

omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms] in
/-- Transport the actual degree-zero comparison along a natural isomorphism
of the original functor. -/
def transport (β : Φ ≅ Ψ) : Ψ ⋙ T' ⟶ T ⋙ Ψ :=
  Functor.whiskerRight β.inv T' ≫ e ≫ Functor.whiskerLeft T β.hom

omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms] in
/-- Transport uses the inverse at the source and the forward component at
the actual target object. -/
theorem transport_app (β : Φ ≅ Ψ) (M : A) :
    (transport e β).app M =
      T'.map (β.inv.app M) ≫ e.app M ≫ β.hom.app (T.obj M) := rfl

include he in
omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms] in
/-- The transported comparison preserves the original coaugmentation. -/
theorem transport_comm (β : Φ ≅ Ψ) (M : A) :
    η'.app (Ψ.obj M) ≫ (transport e β).app M = Ψ.map (η.app M) := by
  rw [transport_app, ← Category.assoc, ← η'.naturality, Category.assoc]
  rw [← Category.assoc (η'.app (Φ.obj M)), he M]
  rw [β.hom.naturality]
  change β.inv.app M ≫ β.hom.app M ≫ Ψ.map (η.app M) = Ψ.map (η.app M)
  rw [Iso.inv_hom_id_app_assoc]

omit [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms] in
/-- The natural isomorphism itself satisfies the degree-zero comparison
square for the transported map. -/
theorem transport_hom_comm (β : Φ ≅ Ψ) (M : A) :
    T'.map (β.hom.app M) ≫ (transport e β).app M =
      e.app M ≫ β.hom.app (T.obj M) := by
  rw [transport_app, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Transported degree-zero maps induce actual chain maps of the original
iterated-cokernel complexes. -/
def transportComplexMap (β : Φ ≅ Ψ) (M : A) :
    complex T' η' (Ψ.obj M) ⟶
      (Ψ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex T η M) :=
  complexMap (transport e β) (transport_comm e he β) M

/-- The constructed transported chain map agrees with transport of the
original chain map in every degree. -/
theorem transportComplexMap_comm (β : Φ ≅ Ψ) (M : A) :
    (functor T' η').map (β.hom.app M) ≫ transportComplexMap e he β M =
      complexMap e he M ≫
        (NatTrans.mapHomologicalComplex β.hom (ComplexShape.up ℕ)).app (complex T η M) :=
  complexMap_transformation e (transport e β) β.hom (transport_hom_comm e β)
    he (transport_comm e he β) M

end Langlands.Cohomology.CokernelComplex.Lax
