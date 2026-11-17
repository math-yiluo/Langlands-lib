import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Subobject.Basic

/-! # Module sheaf subobjects detected by actual stalk images -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.ModuleSheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
  {A B M N : X.Sheaf (ModuleCat.{u} R)}

/-- Two actual module sheaf morphisms agree if they agree on all actual stalks. -/
theorem hom_ext_stalk {f g : M ⟶ N}
    (h : ∀ x : X, (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f.hom =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map g.hom) : f = g := by
  apply Sheaf.hom_ext
  ext U s
  apply TopCat.Presheaf.section_ext N U.unop
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply, h x]

/-- The actual linear image of a module sheaf map at a point. -/
def stalkImage (f : M ⟶ N) (x : X) :
    Submodule R (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) N.obj x) :=
  LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f.hom).hom

/-- Inclusion of actual sheaf subobjects is equivalent to inclusion on every stalk. -/
theorem subobject_mk_le_iff_stalkImage_le (f : A ⟶ N) (g : B ⟶ N)
    [Mono f] [Mono g] :
    Subobject.mk f ≤ Subobject.mk g ↔ ∀ x : X, stalkImage f x ≤ stalkImage g x := by
  constructor
  · intro h x v hv
    let S := TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x
    obtain ⟨a, rfl⟩ := hv
    refine ⟨S.map (Subobject.ofMkLEMk f g h) a, ?_⟩
    have e := congrArg (fun k => S.map k) (Subobject.ofMkLEMk_comp h)
    rw [S.map_comp] at e
    exact congrArg (fun k => k a) e
  · intro h
    have hz : f ≫ cokernel.π g = 0 := by
      apply hom_ext_stalk
      intro x
      let S := TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x
      change S.map (f ≫ cokernel.π g) = S.map 0
      rw [S.map_comp, S.map_zero]
      ext a
      obtain ⟨b, hb⟩ := h x (show S.map f a ∈ stalkImage f x from ⟨a, rfl⟩)
      change S.map (cokernel.π g) (S.map f a) = 0
      rw [← hb]
      have e := congrArg (fun k => S.map k) (cokernel.condition g)
      rw [S.map_comp, S.map_zero] at e
      exact congrArg (fun k => k b) e
    exact Subobject.mk_le_mk_of_comm (Abelian.monoLift g f hz)
      (Abelian.monoLift_comp g f hz)

/-- Equality of actual sheaf subobjects is equivalent to equality of every stalk image. -/
theorem subobject_mk_eq_iff_stalkImage_eq (f : A ⟶ N) (g : B ⟶ N)
    [Mono f] [Mono g] :
    Subobject.mk f = Subobject.mk g ↔ ∀ x : X, stalkImage f x = stalkImage g x := by
  constructor
  · intro h x
    exact le_antisymm
      ((subobject_mk_le_iff_stalkImage_le f g).mp h.le x)
      ((subobject_mk_le_iff_stalkImage_le g f).mp h.ge x)
  · intro h
    exact le_antisymm
      ((subobject_mk_le_iff_stalkImage_le f g).mpr (fun x => (h x).le))
      ((subobject_mk_le_iff_stalkImage_le g f).mpr (fun x => (h x).ge))

end Langlands.ModuleSheaf
