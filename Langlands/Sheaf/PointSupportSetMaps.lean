import Langlands.Sheaf.PointSupport

/-! # Support transport by natural maps of underlying sets -/

noncomputable section

namespace Langlands.Sheaf.PointSupport

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type uI} (points : I → J.Point.{w})
variable {R : Type w} [CommRing R]
variable {F G : Cᵒᵖ ⥤ ModuleCat.{w} R}
section NaturalMap

variable (a : F ⋙ forget (ModuleCat R) ⟶ G ⋙ forget (ModuleCat R))
variable (ha : ∀ U, a.app U 0 = 0)

include ha

/-- A natural map of underlying sets preserving zero carries zero germs to zero germs. -/
theorem toPresheafFiber_setMap_eq_zero [LocallySmall.{w} C]
    (i : I) (X : C) (x : (points i).fiber.obj X) (s : F.obj (op X))
    (hs : (points i).toPresheafFiber X x F s = 0) :
    (points i).toPresheafFiber X x G (a.app (op X) s) = 0 := by
  have hs' : (points i).toPresheafFiber X x F s =
      (points i).toPresheafFiber X x F 0 := by simpa using hs
  obtain ⟨Y, f, y, hy, hlocal⟩ :=
    ((points i).toPresheafFiber_eq_iff' X x s 0).mp hs'
  have hn := ConcreteCategory.congr_hom (a.naturality f.op) s
  change a.app (op Y) (F.map f.op s) = G.map f.op (a.app (op X) s) at hn
  have hz : G.map f.op (a.app (op X) s) = 0 := by
    rw [← hn, hlocal, map_zero, ha]
  rw [← hy, ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hz, map_zero]

/-- Natural maps of underlying sets preserving zero shrink actual germ supports. -/
theorem support_setMap_subset [LocallySmall.{w} C] {X : C} (s : F.obj (op X)) :
    support points G (a.app (op X) s) ⊆ support points F s := by
  rintro i ⟨x, hx⟩
  exact ⟨x, fun hs => hx (toPresheafFiber_setMap_eq_zero points a ha i X x s hs)⟩

/-- A zero-preserving natural map carries compactly supported sections to compactly
supported sections, without any linearity requirement. -/
theorem IsCompactlySupported.setMap [LocallySmall.{w} C] [TopologicalSpace I]
    {X : C} {s : F.obj (op X)} (hs : IsCompactlySupported points F s) :
    IsCompactlySupported points G (a.app (op X) s) := by
  obtain ⟨K, hK, hsK⟩ := hs
  exact ⟨K, hK, (support_setMap_subset points a ha s).trans hsK⟩

end NaturalMap

/-- A natural zero-preserving section of a sheaf morphism lifts actual compact
sections, even if the section is only a map of underlying sets. -/
theorem sheafCompactSections_map_surjective_of_setSection
    [LocallySmall.{w} C] [TopologicalSpace I]
    {E E' : Sheaf J (ModuleCat.{w} R)} (f : E ⟶ E')
    (a : E'.obj ⋙ forget (ModuleCat R) ⟶ E.obj ⋙ forget (ModuleCat R))
    (ha : ∀ U, a.app U 0 = 0)
    (hfa : ∀ U s, f.hom.app U (a.app U s) = s) (X : C) :
    Function.Surjective ((sheafCompactSections J points R X).map f) := by
  intro s
  exact ⟨⟨a.app (op X) s.val, s.property.setMap points a ha⟩,
    Subtype.ext (hfa (op X) s.val)⟩

end Langlands.Sheaf.PointSupport
