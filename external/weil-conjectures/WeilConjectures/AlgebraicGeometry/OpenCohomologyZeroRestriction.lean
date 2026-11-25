/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCohomologyZeroSections

/-! # Degree-zero comparison and restriction of opens

Source: Stacks Project, Tags 01DZ and 01E1, restriction on sheaf cohomology.
(blueprint: lem-sc-open-cohomology-zero-restriction).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
/-- The canonical degree-zero comparison intertwines derived restriction and sections.
Source: Stacks Project, Tags 01DZ and 01E1.
(blueprint: lem-sc-open-cohomology-zero-restriction).

Proof: The sectionwise restriction is a natural transformation between the left exact
open-sections functors. Its right-derived transformation in degree zero commutes with
the canonical maps toRightDerivedZero: use the same injective resolution of M on both
sides, and naturality of the map from the zeroth cycles to zeroth homology for the
restriction cochain map. Both toRightDerivedZero maps are isomorphisms. Cancel them
to obtain the naturality square for their inverses rightDerivedZeroIsoSelf. Evaluating
that square at M and then at x is the displayed equation. Since no injectivity,
quasi-coherence or affine assumption on M is used, this includes all opens, including
the empty open. -/
theorem openCohomologyZeroSectionsIso_restriction (X : RingedSpace.{u})
    {U V : Opens X} (i : V ⟶ U) (M : SheafOfModules.{u} (moduleRings X))
    (x : (openModuleCohomology X 0 U).obj M) :
    (openCohomologyZeroSectionsIso X V).hom.app M
        ((openModuleCohomologyRestriction X 0 i).app M x) =
      M.val.presheaf.map i.op ((openCohomologyZeroSectionsIso X U).hom.app M x) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  let F := openModuleSections X U
  let G := openModuleSections X V
  let α : F ⟶ G :=
    Functor.whiskerLeft (SheafOfModules.forget (moduleRings X) ⋙
      PresheafOfModules.toPresheaf (moduleRings X).obj)
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map i.op)
  let P := injectiveResolution M
  let φ := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex
  have hc : α.app M ≫ P.toRightDerivedZero' G =
      P.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap φ 0 := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).mp
    rw [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      Category.assoc, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact (α.naturality (P.ι.f 0)).symm
  have h : α.app M ≫ G.toRightDerivedZero.app M =
      F.toRightDerivedZero.app M ≫ (NatTrans.rightDerived α 0).app M := by
    rw [P.toRightDerivedZero_eq F, P.toRightDerivedZero_eq G,
      P.rightDerived_app_eq α 0]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change α.app M ≫ P.toRightDerivedZero' G ≫
        ((G.mapHomologicalComplex _).obj P.cocomplex).homologyπ 0 ≫
          (P.isoRightDerivedObj G 0).inv =
      P.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex _).obj P.cocomplex).homologyπ 0 ≫
          HomologicalComplex.homologyMap φ 0 ≫ (P.isoRightDerivedObj G 0).inv
    rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc, hc,
      Category.assoc]
  have h' : (NatTrans.rightDerived α 0).app M ≫ G.rightDerivedZeroIsoSelf.hom.app M =
      F.rightDerivedZeroIsoSelf.hom.app M ≫ α.app M := by
    rw [← cancel_epi (F.toRightDerivedZero.app M), ← Category.assoc, ← h]
    simp only [Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app,
      Category.comp_id, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc]
  exact congrArg (fun f ↦ f x) h'

end AlgebraicGeometry.RingedSpace
