/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Natural comparison with the source library's ordinary cohomology

Source: Stacks Project, Tag 03FD, and the Ext definition of sheaf cohomology.
(blueprint: lem-sc-module-cohomology-source-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Module right-derived sections agree naturally with the ordinary Ext model H.
Source: Stacks Project, Tag 03FD, Lemma 21.12.4; Mathlib's constant-sheaf and
free-abelian-Yoneda adjunctions identify the two terminal Ext source objects.
(blueprint: lem-sc-module-cohomology-source-comparison)

Proof: Use zariskiModuleAbelianCohomologyAgree to compare module right-derived
sections with Ext from the sheafified free abelian representable at the top open.
That source object is canonically isomorphic to the constant integer sheaf:
for every abelian sheaf A, the free-abelian-Yoneda/sheafification adjunctions
identify maps from the former with A(top); the constant-sheaf adjunction identifies
maps from the latter with the same group, by evaluation at 1. These additive
identifications are natural in A, so Yoneda yields the source isomorphism.
Precomposition by it identifies the Ext groups, naturally in the target sheaf,
in every degree. Reindex any differing HasExt models using homAddEquiv through
the same derived category; postcomposition commutes with this reindexing.
Compose the natural isomorphisms and forget the module structure on the first
group. The resulting naturality square is exactly H.map, since H and H.map are
defined using the underlying abelian sheaf. This construction includes q=0,
zero modules and the empty scheme. No quasi-coherence is required. -/
theorem exists_moduleCohomology_source_comparison (X : Scheme.{u}) (q : ℕ) :
    ∃ e : ∀ F : X.Modules,
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+ H F q,
      ∀ (F G : X.Modules) (φ : F ⟶ G)
          (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
        e G (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
          H.map φ q (e F x) := by
  classical
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  obtain ⟨a, ha⟩ := zariskiModuleAbelianCohomologyAgree X
  let e0 : yoneda.obj (⊤ : TopologicalSpace.Opens X.carrier) ⋙ AddCommGrpCat.free ≅
      (Functor.const (TopologicalSpace.Opens X.carrier)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : TopologicalSpace.Opens X.carrier)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro z
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X.carrier)
    AddCommGrpCat).mapIso e0
  let t (F : X.Modules) :
      @CategoryTheory.Sheaf.H' _ _ _ _
        (hasExt_of_enoughInjectives _) ((SheafOfModules.toSheaf
          (moduleRings X.toRingedSpace)).obj F) q ⊤ ≃+ H F q :=
    (Abelian.Ext.precompAddEquiv eS ((SheafOfModules.toSheaf
      (moduleRings X.toRingedSpace)).obj F) q).symm
  refine ⟨fun F ↦ (((a q).app F).addCommGroupIsoToAddEquiv).trans (t F), ?_⟩
  intro F G φ x
  have hα := congrArg (fun f ↦ f.hom x) ((a q).hom.naturality φ)
  change t G (((a q).hom.app G)
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x)) = _
  change ((a q).hom.app G)
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
      (((Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X.carrier) q).map
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ)).app (op ⊤))
        (((a q).hom.app F) x) at hα
  erw [hα]
  change (Abelian.Ext.mk₀ eS.inv).comp
      (((((a q).hom.app F) x)).comp
        (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ))
        (add_zero q)) (zero_add q) =
    ((Abelian.Ext.mk₀ eS.inv).comp (((a q).hom.app F) x) (zero_add q)).comp
      (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ))
      (add_zero q)
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

end AlgebraicGeometry.Scheme.Modules
