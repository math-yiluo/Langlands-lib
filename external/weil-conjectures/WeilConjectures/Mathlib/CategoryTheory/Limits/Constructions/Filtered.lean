/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Functors preserving finite coproducts and filtered colimits preserve coproducts

A coproduct `∐ f` is the filtered colimit of the finite subcoproducts
(`CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`). Hence a
functor preserving finite coproducts and colimits indexed by `Finset (Discrete α)` preserves
coproducts indexed by `α`
(`CategoryTheory.Limits.preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts`).
-/

@[expose] public section

namespace CategoryTheory.Limits

open CoproductsFromFiniteFiltered

variable {C D : Type*} [Category* C] [Category* D] {α : Type*}
  [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  [HasColimitsOfShape (Discrete α) C] [HasColimitsOfShape (Discrete α) D]
  [HasColimitsOfShape (Finset (Discrete α)) C]
  (G : C ⥤ D) [PreservesFiniteCoproducts G] [PreservesColimitsOfShape (Finset (Discrete α)) G]

/-- The leg at a finite subset `S` of the cocone, with vertex `∐ (G ∘ f)`, over the image under
`G` of the diagram of finite subcoproducts of `f`. -/
noncomputable def finiteSubcoproductsMapLeg (f : α → C) (S : Finset (Discrete α)) :
    G.obj (∐ fun x : S ↦ f x.1.as) ⟶ ∐ fun a ↦ G.obj (f a) :=
  inv (sigmaComparison G fun x : S ↦ f x.1.as) ≫
    Sigma.desc fun x ↦ Sigma.ι (fun a ↦ G.obj (f a)) x.1.as

omit [HasColimitsOfShape (Discrete α) C] [HasColimitsOfShape (Finset (Discrete α)) C]
  [PreservesColimitsOfShape (Finset (Discrete α)) G] in
@[reassoc]
lemma map_ι_finiteSubcoproductsMapLeg (f : α → C) (S : Finset (Discrete α)) (x : S) :
    G.map (Sigma.ι (fun x : S ↦ f x.1.as) x) ≫ finiteSubcoproductsMapLeg G f S =
      Sigma.ι (fun a ↦ G.obj (f a)) x.1.as := by
  simp [finiteSubcoproductsMapLeg]

/-- The cocone, with vertex `∐ (G ∘ f)`, over the image under `G` of the diagram of finite
subcoproducts of `f`. -/
noncomputable def finiteSubcoproductsMapCocone (f : α → C) :
    Cocone (liftToFinsetObj (Discrete.functor f) ⋙ G) where
  pt := ∐ fun a ↦ G.obj (f a)
  ι :=
    { app S := finiteSubcoproductsMapLeg G f S
      naturality S S' h := by
        rw [← cancel_epi (sigmaComparison G fun x : S ↦ f x.1.as)]
        ext x
        simp [ι_comp_sigmaComparison_assoc, map_ι_finiteSubcoproductsMapLeg] }

/-- A functor preserving finite coproducts and colimits indexed by `Finset (Discrete α)` preserves
coproducts indexed by `α`, a coproduct being the filtered colimit of its finite subcoproducts. -/
lemma isIso_sigmaComparison_of_preservesFiniteCoproducts (f : α → C) :
    IsIso (sigmaComparison G f) := by
  let hc := isColimitOfPreserves G (isColimitFiniteSubproductsCocone f)
  let i : G.obj (∐ f) ⟶ ∐ fun a ↦ G.obj (f a) := hc.desc (finiteSubcoproductsMapCocone G f)
  have hfac (S : Finset (Discrete α)) :
      G.map (Sigma.desc fun s : S ↦ Sigma.ι f s.1.as) ≫ i = finiteSubcoproductsMapLeg G f S :=
    hc.fac (finiteSubcoproductsMapCocone G f) S
  refine ⟨i, ?_, ?_⟩
  · ext a
    have h : Sigma.ι f a = Sigma.ι (fun x : ({⟨a⟩} : Finset (Discrete α)) ↦ f x.1.as)
        ⟨⟨a⟩, by simp⟩ ≫
          Sigma.desc fun s : ({⟨a⟩} : Finset (Discrete α)) ↦ Sigma.ι f s.1.as := by simp
    rw [ι_comp_sigmaComparison_assoc, h, G.map_comp, Category.assoc, hfac,
      map_ι_finiteSubcoproductsMapLeg, Category.comp_id]
  · have hext {Z : D} {a b : G.obj (∐ f) ⟶ Z}
        (h : ∀ S : Finset (Discrete α), G.map (Sigma.desc fun s : S ↦ Sigma.ι f s.1.as) ≫ a =
          G.map (Sigma.desc fun s : S ↦ Sigma.ι f s.1.as) ≫ b) : a = b :=
      hc.hom_ext h
    refine hext fun S ↦ ?_
    rw [Category.comp_id, ← Category.assoc, hfac,
      ← cancel_epi (sigmaComparison G fun x : S ↦ f x.1.as)]
    ext x
    simp [finiteSubcoproductsMapLeg]


/-- A functor preserving finite coproducts and colimits indexed by `Finset (Discrete α)` preserves
coproducts indexed by `α`. -/
lemma preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts :
    PreservesColimitsOfShape (Discrete α) G where
  preservesColimit {K} :=
    have := isIso_sigmaComparison_of_preservesFiniteCoproducts G (K.obj ∘ Discrete.mk)
    have := PreservesCoproduct.of_iso_comparison G (K.obj ∘ Discrete.mk)
    preservesColimit_of_iso_diagram G (Discrete.natIsoFunctor (F := K)).symm

end CategoryTheory.Limits
