/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.DirectSum.Basic
import WeilConjectures.AlgebraicGeometry.DerivedGlobalSectionsPreservesCoproducts
import WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Zeroth derived global sections of a coproduct
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph (blueprint: lem-pc-derived-global-sections-cohomology-coproduct).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- Zeroth derived global sections commutes with coproducts of quasi-coherent complexes.
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph (blueprint: lem-pc-derived-global-sections-cohomology-coproduct).
Proof: Let a:X → Spec(ULift ℤ) be the structure morphism. Quasi-compactness and
quasi-separatedness of X make a quasi-compact and quasi-separated. Derived direct image
preserves the displayed ambient coproduct of quasi-coherent complexes. The affine derived
equivalence on Spec(ULift ℤ) computes global sections of Ra_* by module complexes.
Derived global sections of Ra_* are those of the original complex, by composition of
pushforward and the injective-resolution computation. The affine equivalence preserves
coproducts, which are represented termwise in module complexes. Exactness of module sums
identifies their H^0 with the sum of their H^0. Forgetting the global-section ring action
preserves and reflects this bijection. All comparisons are natural in the coprojections,
so their composite is the displayed DirectSum.toAddMonoid map. For the empty family both
sides are zero; the same argument applies to zero summands and arbitrary shifts. -/
theorem derivedGlobalSections_cohomology_coproduct (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let F := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    ∀ (I : Type u) (E : I → schemeDerivedQCohCategory X)
      (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S),
      IsColimit (Cofan.mk S ι) →
      Function.Bijective (DirectSum.toAddMonoid (fun i ↦ (F.map (ι i)).hom) :
        (⨁ i : I, F.obj (E i).obj) →+ F.obj S) := by
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
  intro F I E S ι hι
  let R := (moduleRings X.toRingedSpace).obj.obj (op ⊤)
  let G := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  have hG : IsColimit (Cofan.mk (G.obj S) (fun i ↦ G.map (ι i))) :=
    (derivedGlobalSections_preserves_coproducts X I E S ι hι).some
  have hH := (derivedModuleHomology_coproduct R 0 I
    (fun i ↦ G.obj (E i).obj) (G.obj S) (fun i ↦ G.map (ι i)) hG).some
  let Z := fun i ↦ H.obj (G.obj (E i).obj)
  let tH := (ModuleCat.coproductCoconeIsColimit Z).coconePointUniqueUpToIso hH
  let d : ModuleCat.of R (⨁ i, Z i) ⟶ H.obj (G.obj S) :=
    ModuleCat.ofHom (DirectSum.toModule R I _ (fun i ↦ (H.map (G.map (ι i))).hom))
  have hd : d = tH.hom := by
    apply (ModuleCat.coproductCoconeIsColimit Z).hom_ext
    intro i
    rw [(ModuleCat.coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom hH i]
    ext x
    exact DirectSum.toModule_lof (R := R) (ι := I) (N := _)
      (φ := fun i ↦ (H.map (G.map (ι i))).hom) i.as x
  have : IsIso d := by rw [hd]; infer_instance
  have hdB := ConcreteCategory.bijective_of_isIso d
  change Function.Bijective (DirectSum.toAddMonoid
    (fun i ↦ (H.map (G.map (ι i))).hom.toAddMonoidHom))
  rw [← DirectSum.coe_toModule_eq_coe_toAddMonoid R I]
  exact hdB

end AlgebraicGeometry
