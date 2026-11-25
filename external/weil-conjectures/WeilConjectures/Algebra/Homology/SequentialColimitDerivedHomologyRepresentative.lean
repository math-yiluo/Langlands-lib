/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Finite-stage representatives for zeroth cohomology
Source: Stacks Project, Tag 00DB. -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
variable (A : Type u) [CommRing A]

set_option backward.isDefEq.respectTransparency false in
/-- Tag 00DB, expressed as preservation of colimits by short-complex homology.
The evaluation and colimit homology isomorphisms commute with the cocone legs by
`ShortComplex.homologyMap_mapNatTrans`. -/
private theorem shortComplexHomologyPreserves
    {I : Type} [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor (ModuleCat.{u} A)) := by
  classical
  refine ⟨fun {F} ↦ ?_⟩
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) :=
    AB5OfSize_shrink.{0, 0, u, u} _
  have : (colim (J := I) (C := ModuleCat.{u} A)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
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
/-- Every zeroth cohomology class of a sequential colimit is represented at a finite stage.
Source: Stacks Project, Tag 00DB.
(blueprint: lem-sc-sequential-colimit-derived-homology-representative)

Proof: exactness of filtered colimits of modules makes short-complex homology preserve
filtered colimits. The functor taking the three adjacent terms of a complex preserves
colimits because each evaluation does. Thus complex homology preserves this colimit.
Transport the resulting colimit cocone along the canonical comparison between derived
and complex homology, then use the concrete colimit representative theorem. No boundedness
is needed, since only the three terms adjacent to degree zero enter the argument. -/
theorem sequentialColimit_derivedHomology_representative
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    ∀ x : H.obj (DerivedCategory.Q.obj (colimit D)),
      ∃ (e : ℕ) (z : H.obj (DerivedCategory.Q.obj (D.obj e))),
        H.map (DerivedCategory.Q.map (colimit.ι D e)) z = x := by
  dsimp only
  classical
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) 0
  have : PreservesColimitsOfShape ℕ (ShortComplex.homologyFunctor (ModuleCat.{u} A)) :=
    shortComplexHomologyPreserves A
  have : PreservesColimitsOfShape ℕ
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) 0) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
  have : PreservesColimitsOfShape ℕ H :=
    preservesColimitsOfShape_of_natIso
      (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).symm
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _
  let b := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0
  intro x
  obtain ⟨e, z, hz⟩ := Concrete.isColimit_exists_rep (D ⋙ H)
    (isColimitOfPreserves H (colimit.isColimit D)) ((b.app (colimit D)).hom x)
  refine ⟨e, (b.app (D.obj e)).inv z, ?_⟩
  apply (ModuleCat.mono_iff_injective (b.app (colimit D)).hom).mp inferInstance
  have hn := b.hom.naturality (colimit.ι D e)
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (DerivedCategory.Q.map (colimit.ι D e)) ≫ (b.app (colimit D)).hom =
    (b.app (D.obj e)).hom ≫ H.map (colimit.ι D e) at hn
  change ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (DerivedCategory.Q.map (colimit.ι D e)) ≫ (b.app (colimit D)).hom)
      ((b.app (D.obj e)).inv z) = _
  rw [hn]
  change H.map (colimit.ι D e)
    ((b.app (D.obj e)).hom ((b.app (D.obj e)).inv z)) = _
  have hi := ConcreteCategory.congr_hom (b.app (D.obj e)).inv_hom_id z
  change (b.app (D.obj e)).hom ((b.app (D.obj e)).inv z) = z at hi
  rw [hi]
  exact hz

end AlgebraicGeometry
