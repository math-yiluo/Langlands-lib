import Langlands.Representation.Filtration.Definitions
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Twist.SubquotientDefinitions

/-! Transport actual representation filtrations through precomposition and scalar twists. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC uD vD

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- Evaluate the given actual subfunctor along a functor on its input category. -/
def precomp (S : RepSubfunctor F) (J : D ⥤ C) : RepSubfunctor (J ⋙ F) where
  obj X := S.obj (J.obj X)
  map_mem := by
    intro X Y f v hv
    exact S.map_mem (J.map f) hv

@[simp]
theorem precomp_obj (S : RepSubfunctor F) (J : D ⥤ C) (X : D) :
    (S.precomp J).obj X = S.obj (J.obj X) := rfl

variable [TopologicalSpace G]

/-- Retain the same submodules while twisting all ambient actions and maps
by the existing scalar-character functor. -/
def twist (S : RepSubfunctor F) (χ : Induction.SmoothCharacter R G) :
    RepSubfunctor (F ⋙ χ.twistFunctor) where
  obj X := twistSubrepresentation χ.toMonoidHom (S.obj X)
  map_mem := by
    intro X Y f v hv
    exact S.map_mem f hv

@[simp]
theorem twist_obj_toSubmodule (S : RepSubfunctor F)
    (χ : Induction.SmoothCharacter R G) (X : C) :
    ((S.twist χ).obj X).toSubmodule = (S.obj X).toSubmodule := rfl

end RepSubfunctor

namespace RepFunctorFiltration

variable {n : ℕ}

/-- Precomposition preserves the specified indices, spaces and endpoints. -/
def precomp (s : RepFunctorFiltration F n) (J : D ⥤ C) :
    RepFunctorFiltration (J ⋙ F) n where
  step k := (s.step k).precomp J
  monotone X := s.monotone (J.obj X)
  zero X := s.zero (J.obj X)
  top X := s.top (J.obj X)

@[simp]
theorem precomp_step_obj (s : RepFunctorFiltration F n) (J : D ⥤ C)
    (k : Fin (n + 1)) (X : D) :
    ((s.precomp J).step k).obj X = (s.step k).obj (J.obj X) := rfl

variable [TopologicalSpace G]

/-- Twisting preserves the fixed filtration order and underlying submodules. -/
def twist (s : RepFunctorFiltration F n) (χ : Induction.SmoothCharacter R G) :
    RepFunctorFiltration (F ⋙ χ.twistFunctor) n where
  step k := (s.step k).twist χ
  monotone X := by
    intro i j hij
    exact s.monotone X hij
  zero X := by
    change twistSubrepresentation χ.toMonoidHom ((s.step 0).obj X) = ⊥
    rw [s.zero X]
    exact (twistSubrepresentationOrderIso χ.toMonoidHom (F.obj X).ρ).map_bot
  top X := by
    change twistSubrepresentation χ.toMonoidHom ((s.step (Fin.last n)).obj X) = ⊤
    rw [s.top X]
    exact (twistSubrepresentationOrderIso χ.toMonoidHom (F.obj X).ρ).map_top

@[simp]
theorem twist_step_toSubmodule (s : RepFunctorFiltration F n)
    (χ : Induction.SmoothCharacter R G) (k : Fin (n + 1)) (X : C) :
    (((s.twist χ).step k).obj X).toSubmodule = ((s.step k).obj X).toSubmodule := rfl

end RepFunctorFiltration

end Langlands
