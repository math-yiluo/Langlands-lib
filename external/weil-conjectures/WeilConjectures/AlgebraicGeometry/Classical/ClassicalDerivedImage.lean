/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Classical cohomology of comparison inverse image

The derived comparison inverse image of a bounded-below étale complex of `Λ`-modules has
classical cohomology sheaves in every degree.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private noncomputable def classicalHomologyIso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _))).inverse ⋙
        (@DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _) q) := by
  let B := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let H := @DerivedCategory.homologyFunctor B _ _ (HasDerivedCategory.standard B) q
  let Q := @DerivedCategory.Q B _ _ (HasDerivedCategory.standard B)
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory B _ _ (HasDerivedCategory.standard B))
  let eQ : DerivedCategory.Q ⋙ e.inverse ≅ Q :=
    Functor.associator Q e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft Q e.unitIso.symm ≪≫ Q.rightUnitor
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) B).preimageIso
      (DerivedCategory.homologyFunctorFactors B q ≪≫
        (@DerivedCategory.homologyFunctorFactors B _ _
          (HasDerivedCategory.standard B) q).symm ≪≫
        Functor.isoWhiskerRight eQ.symm H ≪≫ Functor.associator _ _ _)

/-- Classicality of a module sheaf is invariant under isomorphism: the continuity maps of
isomorphic sheaves differ by the induced isomorphisms on sections and on the colimits. -/
theorem classicalModule_of_iso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
  intro I _ _ P
  have hmap := continuityMap_natural P e.hom.hom
  have : IsIso (continuityMap P F.obj) := hF P
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op
      ((sheafToPresheaf _ _).mapIso e)).hom
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
  rw [hmap]
  infer_instance

/-- The comparison inverse image has classical bounded-below cohomology.
Proof: inverse image commutes with cohomology because it is exact
(`Functor.mapDerivedCategoryPlusHomologyFunctorIso`). Each underived inverse image is
classical by the module equivalence of `proEtaleClassicalSheaves`. Classicality is invariant
under an isomorphism (`classicalModule_of_iso`), by naturality of the continuity map.
Finally compare homology in the small and standard derived models (`classicalHomologyIso`)
using the localization universal property and the equivalence shrinking the Hom types. -/
theorem classicalDerivedImage (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (_hunit : ∀ L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit.app L)) :
    ∀ L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      ClassicalPlus X Λ
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L) := by
  intro L q
  obtain ⟨F, hF, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 Λ
  let M := (DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj L
  have hM : IsClassicalModuleFor X Λ
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj M) := by
    rw [← hF]
    exact (F.obj M).property
  let e := Functor.mapDerivedCategoryPlusHomologyFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) q
  apply classicalModule_of_iso X Λ
    ((e.app L) ≪≫ (classicalHomologyIso X Λ q).app _)
  exact hM

end AlgebraicGeometry.ProEtale

end
