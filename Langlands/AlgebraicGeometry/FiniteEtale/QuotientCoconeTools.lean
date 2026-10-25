import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import Mathlib.CategoryTheory.Limits.Preserves.Basic

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- A surjective cocone map whose fibres are group orbits is a colimit of sets. -/
noncomputable def groupOrbitCoconeIsColimit {G : Type v} [Group G]
    {D : SingleObj G ⥤ Type u} (c : Cocone D)
    (hsurj : Function.Surjective (c.ι.app (SingleObj.star G)))
    (horbit : ∀ x y : D.obj (SingleObj.star G),
      c.ι.app (SingleObj.star G) x = c.ι.app (SingleObj.star G) y →
        ∃ g : G, y = D.map (SingleObj.toEnd G g) x) : IsColimit c := by
  let r := Function.surjInv hsurj
  have hr (y : c.pt) : c.ι.app (SingleObj.star G) (r y) = y :=
    Function.surjInv_eq hsurj y
  have hdesc (s : Cocone D) (x : D.obj (SingleObj.star G)) :
      s.ι.app (SingleObj.star G) (r (c.ι.app (SingleObj.star G) x)) =
        s.ι.app (SingleObj.star G) x := by
    obtain ⟨g, hg⟩ := horbit _ _ (hr (c.ι.app (SingleObj.star G) x))
    calc
      _ = s.ι.app (SingleObj.star G)
          (D.map (SingleObj.toEnd G g) (r (c.ι.app (SingleObj.star G) x))) :=
        (ConcreteCategory.congr_hom (s.w (SingleObj.toEnd G g)) _).symm
      _ = s.ι.app (SingleObj.star G) x := congrArg (s.ι.app (SingleObj.star G)) hg.symm
  refine
    { desc := fun s => TypeCat.ofHom (fun y => s.ι.app (SingleObj.star G) (r y))
      fac := ?_
      uniq := ?_ }
  · intro s j
    cases j
    ext x
    exact hdesc s x
  · intro s m hm
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    exact (ConcreteCategory.congr_hom (hm (SingleObj.star G)) x).trans (hdesc s x).symm

/-- Transfer colimit preservation through the fully faithful finite-set inclusion,
with separate object and morphism universes for the indexing category. -/
theorem fiberFunctor_preservesColimitsOfShape_large
    {S : AlgebraicGeometry.Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : AlgebraicGeometry.Spec (.of Ω) ⟶ S)
    (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) (J : Type v) [Category.{w} J]
    [PreservesColimitsOfShape J (pointFunctor s)] :
    PreservesColimitsOfShape J (fiberFunctor s hfin) := by
  have : PreservesColimitsOfShape J (fiberFunctor s hfin ⋙ FintypeCat.incl) :=
    inferInstanceAs (PreservesColimitsOfShape J (pointFunctor s))
  exact preservesColimitsOfShape_of_reflects_of_preserves _ FintypeCat.incl

end Langlands.AlgebraicGeometry.FiniteEtale
