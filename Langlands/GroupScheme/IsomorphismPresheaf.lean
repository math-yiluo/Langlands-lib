import Langlands.GroupScheme.IsomorphismScheme
import Mathlib.CategoryTheory.Yoneda

/-! # The presheaf of natural local group isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

namespace LocalGroupIso

@[simp] theorem refine_id {T : Over S} (e : LocalGroupIso G H T) :
    e.refine (𝟙 T) = e := by
  apply ext_toFun
  intro W a g
  simp only [refine_toFun, Category.comp_id]

@[simp] theorem refine_comp {T U V : Over S} (e : LocalGroupIso G H T)
    (r : U ⟶ T) (s : V ⟶ U) :
    (e.refine r).refine s = e.refine (s ≫ r) := by
  apply ext_toFun
  intro W a g
  simp only [refine_toFun, Category.assoc]

/-- Local isomorphisms on arbitrary relative tests form a presheaf. -/
def presheaf (G H : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := LocalGroupIso G H T.unop
  map r := TypeCat.ofHom (fun e => e.refine r.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro e
    exact refine_id e
  map_comp r s := by
    apply ConcreteCategory.hom_ext
    intro e
    exact (refine_comp e r.unop s.unop).symm

end LocalGroupIso

namespace GroupIsomorphismScheme

/-- The universal family gives a representation of the entire Isom presheaf. -/
def representableBy (I : GroupIsomorphismScheme G H) :
    (LocalGroupIso.presheaf G H).RepresentableBy I.parameter where
  homEquiv := I.pointsEquiv _
  homEquiv_comp r p := by
    exact (LocalGroupIso.refine_comp I.universalIso p r).symm

/-- A presheaf representation supplies the universal local family and its
classification bijections on every relative scheme test. -/
def ofRepresentableBy {P : Over S}
    (R : (LocalGroupIso.presheaf G H).RepresentableBy P) :
    GroupIsomorphismScheme G H where
  parameter := P
  universalIso := R.homEquiv (𝟙 P)
  bijective T := by
    have h : (fun p : T ⟶ P => (R.homEquiv (𝟙 P)).refine p) = R.homEquiv := by
      funext p
      exact (R.homEquiv_eq p).symm
    rw [h]
    exact R.homEquiv.bijective

@[simp] theorem ofRepresentableBy_universalIso {P : Over S}
    (R : (LocalGroupIso.presheaf G H).RepresentableBy P) :
    (ofRepresentableBy R).universalIso = R.homEquiv (𝟙 P) := rfl

/-- Scheme representability of the Isom presheaf is exactly existence of the
supplied universal-property interface. -/
theorem nonempty_iff_representable :
    Nonempty (GroupIsomorphismScheme G H) ↔
      ∃ P : Over S, Nonempty ((LocalGroupIso.presheaf G H).RepresentableBy P) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨I.parameter, ⟨I.representableBy⟩⟩
  · rintro ⟨P, ⟨R⟩⟩
    exact ⟨ofRepresentableBy R⟩

end GroupIsomorphismScheme

end Langlands.GroupScheme
