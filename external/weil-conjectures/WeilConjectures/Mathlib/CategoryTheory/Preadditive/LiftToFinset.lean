/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Coproducts as filtered colimits of finite coproducts, and additive functors

A coproduct `∐ f` is the filtered colimit of its finite subcoproducts
(`CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`). Hence an
additive functor, which preserves finite coproducts, preserves coproducts of shape `α` as soon
as it preserves colimits of shape `Finset (Discrete α)`
(`CategoryTheory.Limits.preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset`).
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.Limits

open CoproductsFromFiniteFiltered

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- An additive functor `F` between preadditive categories which preserves the filtered colimits
of shape `Finset (Discrete α)` preserves coproducts of shape `α`: a coproduct `∐ f` is the
filtered colimit of its finite subcoproducts, and these are preserved by `F`. -/
lemma preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset (α : Type w)
    [HasColimitsOfShape (Finset (Discrete α)) C] [HasColimitsOfShape (Discrete α) C]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfShape (Finset (Discrete α)) F] :
    PreservesColimitsOfShape (Discrete α) F where
  preservesColimit {K} := by
    let f := K.obj ∘ Discrete.mk
    suffices PreservesColimit (Discrete.functor f) F from
      preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := K)).symm
    refine preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f) ?_
    have hc := isColimitOfPreserves F (isColimitFiniteSubproductsCocone f)
    -- the finite subcoproducts are preserved by the additive functor `F`
    have hS (S : Finset (Discrete α)) : IsColimit (Cofan.mk
        (F.obj (∐ fun x : S ↦ f x.1.as)) fun a ↦ F.map (Sigma.ι (fun x : S ↦ f x.1.as) a)) :=
      (isColimitMapCoconeCofanMkEquiv F _ _).1 (isColimitOfPreserves F (coproductIsCoproduct _))
    let ι (s : Cofan fun a ↦ F.obj (f a)) (S : Finset (Discrete α)) :
        F.obj (∐ fun x : S ↦ f x.1.as) ⟶ s.pt :=
      (hS S).desc (Cofan.mk s.pt fun a ↦ s.inj a.1.as)
    have hι (s : Cofan fun a ↦ F.obj (f a)) (S : Finset (Discrete α)) (a : S) :
        F.map (Sigma.ι (fun x : S ↦ f x.1.as) a) ≫ ι s S = s.inj a.1.as :=
      (hS S).fac (Cofan.mk s.pt fun a ↦ s.inj a.1.as) ⟨a⟩
    let t (s : Cofan fun a ↦ F.obj (f a)) :
        Cocone (liftToFinsetObj (Discrete.functor f) ⋙ F) :=
      { pt := s.pt
        ι :=
          { app := ι s
            naturality := fun S T h ↦ by
              refine Cofan.IsColimit.hom_ext (hS S) _ _ fun a ↦ ?_
              dsimp
              rw [Category.comp_id, hι, ← F.map_comp_assoc, liftToFinsetObj_map]
              erw [colimit.ι_desc]
              exact hι s T ⟨a.1, h.down.down a.2⟩ } }
    have hfac (s : Cofan fun a ↦ F.obj (f a)) (a : α) :
        F.map (Sigma.ι f a) = F.map (Sigma.ι (fun x : ({⟨a⟩} : Finset (Discrete α)) ↦ f x.1.as)
          ⟨⟨a⟩, by simp⟩) ≫ F.map ((finiteSubcoproductsCocone f).ι.app {⟨a⟩}) := by
      rw [← F.map_comp, finiteSubcoproductsCocone_ι_app]
      erw [colimit.ι_desc]
      rfl
    refine (isColimitMapCoconeCofanMkEquiv F f (Sigma.ι f)).2
      (Cofan.IsColimit.mk _ (fun s ↦ hc.desc (t s)) (fun s a ↦ ?_) (fun s m hm ↦ ?_))
    · dsimp
      rw [hfac s a, Category.assoc]
      erw [hc.fac (t s) {⟨a⟩}]
      exact hι s _ _
    · refine hc.hom_ext fun S ↦ ?_
      erw [hc.fac (t s) S]
      refine Cofan.IsColimit.hom_ext (hS S) _ _ fun a ↦ ?_
      dsimp
      rw [hι, ← F.map_comp_assoc, finiteSubcoproductsCocone_ι_app]
      erw [colimit.ι_desc]
      exact hm a.1.as

end CategoryTheory.Limits
