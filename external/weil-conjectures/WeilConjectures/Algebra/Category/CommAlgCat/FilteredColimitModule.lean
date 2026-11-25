/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Filtered colimits of algebras are colimits of the underlying modules

Let `R` be a commutative ring and `F : J ⥤ CommAlgCat R` a filtered diagram. A colimit cocone of
`F` remains a colimit cocone after forgetting to `R`-modules: every compatible family of
`R`-linear maps `F j → P` factors uniquely through the colimit.

## Main statements

- `CommAlgCat.isColimitModuleCatOfIsFiltered`
- `CommAlgCat.existsUnique_linearMap_of_isColimit`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CommAlgCat

variable {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F}

/-- A colimit cocone of a filtered diagram of commutative `R`-algebras is a colimit cocone of the
underlying `R`-modules. -/
noncomputable def isColimitModuleCatOfIsFiltered (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
      forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)).mapCocone c) :=
  isColimitOfPreserves _ hc

/-- A filtered colimit `A = colim A_j` of commutative `R`-algebras is the colimit of the
underlying `R`-modules: for every `R`-module `P` and every compatible family of `R`-linear maps
`f j : A_j → P` there is exactly one `R`-linear map `f : A → P` with `f ∘ ι_j = f j`.
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem existsUnique_linearMap_of_isColimit (hc : IsColimit c) (P : Type u) [AddCommGroup P]
    [Module R P] (f : ∀ j, F.obj j →ₗ[R] P)
    (hf : ∀ ⦃i j : J⦄ (u : i ⟶ j), f j ∘ₗ (F.map u).hom.toLinearMap = f i) :
    ∃! g : c.pt →ₗ[R] P, ∀ j, g ∘ₗ (c.ι.app j).hom.toLinearMap = f j := by
  let G := forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)
  have hc' := isColimitModuleCatOfIsFiltered hc
  let s : Cocone (F ⋙ G) :=
    { pt := ModuleCat.of R P
      ι := { app j := ModuleCat.ofHom (f j)
             naturality i j u := by
               ext x
               exact LinearMap.congr_fun (hf u) x } }
  refine ⟨(hc'.desc s).hom, fun j ↦ ?_, fun g hg ↦ ?_⟩
  · exact congrArg ModuleCat.Hom.hom (hc'.fac s j)
  · have := hc'.uniq s (ModuleCat.ofHom g) fun j ↦ by
      ext x
      exact LinearMap.congr_fun (hg j) x
    exact congrArg ModuleCat.Hom.hom this

end CommAlgCat
