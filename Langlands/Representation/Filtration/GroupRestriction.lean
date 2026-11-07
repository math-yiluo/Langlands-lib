import Langlands.Representation.Filtration.Definitions
import Mathlib.RepresentationTheory.Rep.Res

/-! Restrict the acting group while retaining actual filtration submodules. -/

noncomputable section
open CategoryTheory

namespace Langlands

universe uR uG uH uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {H : Type uH} [Monoid H] {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- Restriction retains the same actual submodules and natural maps. -/
def restrictGroup (S : RepSubfunctor F) (φ : H →* G) :
    RepSubfunctor (F ⋙ Rep.resFunctor φ) where
  obj X :=
    { toSubmodule := (S.obj X).toSubmodule
      apply_mem_toSubmodule h := (S.obj X).apply_mem_toSubmodule (φ h) }
  map_mem := by
    intro X Y f v hv
    exact S.map_mem f hv

@[simp]
theorem restrictGroup_obj_toSubmodule (S : RepSubfunctor F) (φ : H →* G) (X : C) :
    ((S.restrictGroup φ).obj X).toSubmodule = (S.obj X).toSubmodule := rfl

/-- Restriction of a successive quotient is the quotient of the same restricted
submodules, naturally and by the identity on quotient classes. -/
def restrictGroupQuotientIso (S T : RepSubfunctor F) (φ : H →* G) :
    (S.restrictGroup φ).quotientFunctor (T.restrictGroup φ) ≅
      S.quotientFunctor T ⋙ Rep.resFunctor φ :=
  NatIso.ofComponents (fun X => Rep.mkIso
    { toLinearEquiv := LinearEquiv.refl R (S.quotientObj T X)
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
        rfl }) (by
      intro X Y f
      ext v
      rfl)

@[simp]
theorem restrictGroupQuotientIso_hom_projection (S T : RepSubfunctor F)
    (φ : H →* G) (X : C) (v : (T.restrictGroup φ).representation X) :
    ((S.restrictGroupQuotientIso T φ).hom.app X).hom
        (((S.restrictGroup φ).quotientProjection (T.restrictGroup φ) X).hom v) =
      (S.quotientProjection T X).hom v := rfl

end RepSubfunctor

namespace RepFunctorFiltration

variable {n : ℕ}

/-- Restrict every group action, preserving the original submodules and indices. -/
def restrictGroup (s : RepFunctorFiltration F n) (φ : H →* G) :
    RepFunctorFiltration (F ⋙ Rep.resFunctor φ) n where
  step i := (s.step i).restrictGroup φ
  monotone X := s.monotone X
  zero X := by
    apply Subrepresentation.toSubmodule_injective
    change ((s.step 0).obj X).toSubmodule = ⊥
    rw [s.zero X]
    rfl
  top X := by
    apply Subrepresentation.toSubmodule_injective
    change ((s.step (Fin.last n)).obj X).toSubmodule = ⊤
    rw [s.top X]
    rfl

/-- Every restricted grade is the restriction of the original actual grade. -/
def restrictGroupGradedIso (s : RepFunctorFiltration F n) (φ : H →* G) (i : Fin n) :
    (s.restrictGroup φ).graded i ≅ s.graded i ⋙ Rep.resFunctor φ :=
  (s.step i.castSucc).restrictGroupQuotientIso (s.step i.succ) φ

end RepFunctorFiltration

end Langlands
