/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsHomology

/-! # Homology of a coproduct in the derived module category. -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Every degree of derived module homology preserves an ambient coproduct.
Source: Stacks Project, Injectives, Lemma 07D9, and the direct-sum calculation
in the proof of Tag 09M1.
(blueprint: lem-pc-derived-module-homology-coproduct)
Proof: Choose complex representatives K_i of E_i using the localization functor.
The termwise coproduct of the K_i represents their coproduct in the derived
category by Lemma 07D9. Transport the specified colimit to this coproduct along
the unique isomorphism commuting with coprojections. Module coproducts are exact:
kernels, images, and the quotient of cycles by boundaries commute with sums.
Thus complex homology preserves the termwise coproduct. The natural comparison
Q followed by derived homology with complex homology transports this colimit
and its coprojections to the derived category. Finally transport it back along
the colimit isomorphism and the representative isomorphisms. All these comparisons
are natural, so their legs are H(ι_i). This works in every degree, for arbitrary
unbounded complexes, and for empty coproducts (whose homology is zero). -/
theorem derivedModuleHomology_coproduct (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (q : ℤ)
    (I : Type u) (E : I → DerivedCategory (ModuleCat.{u} R))
    (S : DerivedCategory (ModuleCat.{u} R)) (ι : ∀ i, E i ⟶ S)
    (hι : IsColimit (Cofan.mk S ι)) :
    Nonempty (IsColimit (Cofan.mk
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj S)
      (fun i ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map (ι i))))  := by
  classical
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  let K := fun i ↦ Q.objPreimage (E i)
  let e := fun i ↦ Q.objObjPreimageIso (E i)
  let a : Discrete.functor (fun i ↦ Q.obj (K i)) ≅ Discrete.functor E :=
    Discrete.natIso (fun i ↦ e i.as)
  let c := (Cocone.precompose a.hom).obj (Cofan.mk S ι)
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv a _).symm hι
  have hQ := (derivedModuleDirectSums R I K).some
  let t := hQ.coconePointUniqueUpToIso hc
  have hshort := shortComplexHomologyColimit (ModuleCat.{u} R) (Discrete I)
  have := complexHomologyColimit (ModuleCat.{u} R) (Discrete I) hshort q
  have : PreservesColimitsOfShape (Discrete I) (Q ⋙ H) :=
    preservesColimitsOfShape_of_natIso
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q).symm
  have hH : IsColimit ((Q ⋙ H).mapCocone (Cofan.mk (∐ K) (Sigma.ι K))) :=
    isColimitOfPreserves _ (coproductIsCoproduct K)
  have hH' := (Cofan.isColimitMapCoconeEquiv (Q ⋙ H) K _ ) hH
  have hcH : IsColimit (Cofan.mk (H.obj S)
      (fun i ↦ H.map ((e i).hom ≫ ι i))) := by
    apply IsColimit.ofIsoColimit hH'
    refine Cocone.ext (H.mapIso t) ?_
    intro i
    change H.map (Q.map (Sigma.ι K i.as)) ≫ H.map t.hom = H.map ((e i.as).hom ≫ ι i.as)
    rw [← H.map_comp]
    exact congrArg H.map (hQ.comp_coconePointUniqueUpToIso_hom hc i)
  let b : Discrete.functor (fun i ↦ H.obj (Q.obj (K i))) ≅
      Discrete.functor (fun i ↦ H.obj (E i)) :=
    Discrete.natIso (fun i ↦ H.mapIso (e i.as))
  let d := Cofan.mk (H.obj S) (fun i ↦ H.map (ι i))
  have hb : IsColimit ((Cocone.precompose b.hom).obj d) := by
    apply IsColimit.ofIsoColimit hcH
    refine Cocone.ext (Iso.refl _) ?_
    intro i
    simp [d, b, Functor.map_comp]
  exact ⟨(IsColimit.precomposeHomEquiv b d) hb⟩

end AlgebraicGeometry
