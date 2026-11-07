import Langlands.CategoryTheory.Renard.NoetherianCriteria
import Langlands.CategoryTheory.RenardExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Reflection of Renard Noetherianity

The chain argument used in Renard VI.7.5 works for any functor preserving
monomorphisms and reflecting isomorphisms. Faithful left-exact functors
between abelian categories are a special case.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard

universe uC vC uD vD

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  (F : C ⥤ D)

section PreservesMono

variable [F.PreservesMonomorphisms]

/-- Apply the functor to the chosen representative monomorphism of each
actual subobject. -/
def functorSubobjectMap (X : C) : Subobject X →o Subobject (F.obj X) where
  toFun P := Subobject.mk (F.map P.arrow)
  monotone' P Q hPQ :=
    Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE P Q hPQ)) (by
      rw [← F.map_comp, Subobject.ofLE_arrow])

/-- A conservative monomorphism-preserving functor preserves strict
inclusions of actual subobjects. -/
theorem functorSubobjectMap_strictMono [F.ReflectsIsomorphisms] (X : C) :
    StrictMono (functorSubobjectMap F X) := by
  intro P Q hPQ
  apply (Subobject.mk_lt_mk_iff_of_comm
    (F.map (Subobject.ofLE P Q hPQ.le)) (by
      rw [← F.map_comp, Subobject.ofLE_arrow])).mpr
  intro hIso
  have : IsIso (Subobject.ofLE P Q hPQ.le) :=
    isIso_of_reflects_iso _ F
  exact hPQ.ne (Subobject.eq_of_comm
    (asIso (Subobject.ofLE P Q hPQ.le)) (Subobject.ofLE_arrow hPQ.le))

/-- Noetherianity of the image reflects to the source through a functor
preserving monomorphisms and reflecting isomorphisms. -/
theorem noetherianObject_of_functor [F.ReflectsIsomorphisms] (X : C)
    (hX : IsNoetherianObject (F.obj X)) : IsNoetherianObject X := by
  apply (noetherianMathlibComparison C X).mpr
  apply (CategoryTheory.isNoetherianObject_iff_not_strictMono X).mpr
  intro f hf
  have : CategoryTheory.IsNoetherianObject (F.obj X) :=
    (noetherianMathlibComparison D (F.obj X)).mp hX
  exact CategoryTheory.not_strictMono_of_isNoetherianObject
    (fun n => functorSubobjectMap F X (f n))
    ((functorSubobjectMap_strictMono F X).comp hf)

/-- A finite-type-preserving conservative functor into a Noetherian
category transfers the Noetherian-category property, once source unions
are supplied. -/
theorem noetherianCategory_of_functor [F.ReflectsIsomorphisms]
    (hUnions : HasAllSubobjectUnions C)
    (hFinite : ∀ X : C, IsFiniteTypeObject X → IsFiniteTypeObject (F.obj X))
    (hD : IsNoetherianCategory D) : IsNoetherianCategory C :=
  ⟨hUnions, fun X hX => noetherianObject_of_functor F X (hD.2 _ (hFinite X hX))⟩

end PreservesMono

section Abelian

variable [Abelian C] [Abelian D] [F.Additive] [F.Faithful]

/-- The objectwise reflection needed by the faithful exact cuspidal
Jacquet functor of VI.7.2. Only left exactness is needed here. -/
theorem noetherianObject_of_faithful_leftExact
    (hF : SequenceLeftExact F) (X : C)
    (hX : IsNoetherianObject (F.obj X)) : IsNoetherianObject X := by
  have : F.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preserves_shortExact_left F
      (fun S hS => hF S ⟨hS.exact, hS.mono_f⟩)
  exact noetherianObject_of_functor F X hX

/-- The categorical transfer step in VI.7.5, with every substantive
representation-theoretic input explicit. -/
theorem noetherianCategory_of_faithful_leftExact
    (hF : SequenceLeftExact F)
    (hUnions : HasAllSubobjectUnions C)
    (hFinite : ∀ X : C, IsFiniteTypeObject X → IsFiniteTypeObject (F.obj X))
    (hD : IsNoetherianCategory D) : IsNoetherianCategory C :=
  ⟨hUnions, fun X hX =>
    noetherianObject_of_faithful_leftExact F hF X (hD.2 _ (hFinite X hX))⟩

end Abelian

end Langlands.Renard
