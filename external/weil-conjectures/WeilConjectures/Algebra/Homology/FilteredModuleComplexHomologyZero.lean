/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Eventual vanishing of a class in a filtered colimit of module complexes

Source: Stacks Project, Tags 00DB and 08DC.
(blueprint: lem-sc-filtered-module-complex-homology-zero).
-/

@[expose] public section

universe u

namespace CategoryTheory
open Limits

set_option backward.isDefEq.respectTransparency false in
/-- Tag 00DB, expressed as preservation of colimits by short-complex homology.
The evaluation and colimit homology isomorphisms commute with the cocone legs by
`ShortComplex.homologyMap_mapNatTrans`. -/
private theorem shortComplexHomologyPreserves
    (A : Type u) [CommRing A] {I : Type} [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor (ModuleCat.{u} A)) := by
  classical
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_shrink _
  refine ⟨fun {F} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence I (ModuleCat.{u} A)).inverse.obj F
  let e : S.homology ≅ F ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} A) :=
    NatIso.ofComponents
      (fun i ↦ (S.mapHomologyIso ((evaluation I (ModuleCat.{u} A)).obj i)).symm)
      (by
        intro i j f
        have h := S.homologyMap_mapNatTrans ((evaluation I (ModuleCat.{u} A)).map f)
        change ShortComplex.homologyMap (F.map f) = _ at h
        change S.homology.map f ≫
          (S.mapHomologyIso ((evaluation I (ModuleCat.{u} A)).obj j)).inv =
          (S.mapHomologyIso ((evaluation I (ModuleCat.{u} A)).obj i)).inv ≫
            ShortComplex.homologyMap (F.map f)
        rw [h]
        simp)
  let a : colimit (F ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} A)) ≅
      (ShortComplex.colimitCocone F).pt.homology :=
    (colim.mapIso e).symm ≪≫ (S.mapHomologyIso colim).symm
  refine preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone F) ?_
  apply IsColimit.ofIsoColimit (colimit.isColimit _)
  refine Cocone.ext a ?_
  intro i
  have h := S.homologyMap_mapNatTrans (colim.ι (C := (ModuleCat.{u} A)) i)
  change ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i) = _ at h
  change colimit.ι _ i ≫ a.hom =
    ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i)
  rw [h]
  simp [a, e]

set_option backward.isDefEq.respectTransparency false in
/-- A cohomology class zero in the colimit is killed at a later stage.
Source: Stacks Project, Tag 00DB (exactness) and Tag 08DC (Koszul application).
(blueprint: lem-sc-filtered-module-complex-homology-zero)

Proof: Colimits of modules indexed by the natural numbers are exact. Apply their
exact colimit functor to the three adjacent terms of a complex: it preserves
kernels and cokernels and therefore homology. Evaluation at each index has the
same property. The homology comparison is natural for the cocone legs, so these
legs give a colimit cocone on the diagram of homology modules. The forgetful
functor to types preserves this filtered colimit. Equality between the image of
x and that of zero is witnessed at one common later stage; in the natural-number
preorder both transition arrows to that stage coincide. Linearity preserves zero,
giving the asserted equation. Zero complexes and zero classes are included. -/
theorem filteredModuleComplex_homology_eventually_zero
    (A : Type u) [CommRing A] (D : ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℤ) (e : ℕ) (x : (D.obj e).homology n)
    (hx : HomologicalComplex.homologyMap (colimit.ι D e) n x = 0) :
    ∃ (b : ℕ) (h : e ≤ b),
      HomologicalComplex.homologyMap (D.map (homOfLE h)) n x = 0 := by
  classical
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n
  have : PreservesColimitsOfShape ℕ
      (ShortComplex.homologyFunctor (ModuleCat.{u} A)) := shortComplexHomologyPreserves A
  have : PreservesColimitsOfShape ℕ
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) (.up ℤ) n) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ ((ComplexShape.up ℤ).prev n)) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ n) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ ((ComplexShape.up ℤ).next n)) hs
  have : PreservesColimitsOfShape ℕ H := preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} A) (.up ℤ) n).symm
  let c := H.mapCocone (colimit.cocone D)
  have hc : IsColimit c := isColimitOfPreserves H (colimit.isColimit D)
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have heq : c.ι.app e x = c.ι.app e (0 : (D.obj e).homology n) := by
    change H.map ((colimit.cocone D).ι.app e) x =
      H.map ((colimit.cocone D).ι.app e) 0
    simp only [colimit.cocone_ι, colimit.cocone_x, Functor.const_obj_obj, H,
      HomologicalComplex.homologyFunctor_map]
    change HomologicalComplex.homologyMap (colimit.ι D e) n x =
      HomologicalComplex.homologyMap (colimit.ι D e) n 0
    exact hx.trans (map_zero (HomologicalComplex.homologyMap (colimit.ι D e) n).hom).symm
  obtain ⟨b, g, k, hb⟩ := Concrete.isColimit_exists_of_rep_eq (D ⋙ H) hc x 0 heq
  refine ⟨b, leOfHom g, ?_⟩
  change HomologicalComplex.homologyMap (D.map g) n x =
    HomologicalComplex.homologyMap (D.map k) n 0 at hb
  have hg : g = homOfLE (leOfHom g) := Subsingleton.elim _ _
  simpa only [hg, map_zero] using hb

end CategoryTheory
