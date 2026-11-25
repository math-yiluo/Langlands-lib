/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # The explicit Ext-to-resolution-sections comparison

Source: Stacks Project, Tag 06XR and evaluation at 1 in the constant integer sheaf.
(blueprint: def-weil-pbc-ext-resolution-sections-iso)
-/

@[expose] public section

universe u
open CategoryTheory CochainComplex HomComplex Limits Opposite
namespace AlgebraicGeometry.SheafPullbackResolution

/-- (blueprint: def-weil-pbc-ext-resolution-sections-iso) -/
noncomputable abbrev ZSheaf (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- (blueprint: def-weil-pbc-ext-resolution-sections-iso) -/
noncomputable def sectionsEquiv (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (ZSheaf X ⟶ F) ≃+ (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F :=
  ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: def-weil-pbc-ext-resolution-sections-iso) -/
noncomputable def complexSectionsIso (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj (ZSheaf X)) K ≅
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      (sectionsEquiv X (K.X n))).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        have h : sectionsEquiv X (K.X j) (a ≫ K.d i j) =
            (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (K.d i j)
              (sectionsEquiv X (K.X i) a) := by
          dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
          rw [Adjunction.homEquiv_naturality_right]
          rfl
        simpa [HomComplex, Cochain.δ_fromSingleMk,
          Cochain.fromSingleEquiv_fromSingleMk] using! h.symm)

/-- (blueprint: def-weil-pbc-ext-resolution-sections-iso) -/
noncomputable def classSectionsIso (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (n : ℤ) :
    AddCommGrpCat.of
        (CohomologyClass ((CochainComplex.singleFunctor _ 0).obj (ZSheaf X)) K n) ≅
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
        K).homology n :=
  (leftHomologyData _ K n).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (complexSectionsIso X K)

/-- The canonical comparison of Ext cohomology with sections of the chosen resolution.
Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
(blueprint: def-weil-pbc-ext-resolution-sections-iso)

The Ext/resolution equivalence sends an Ext class to its cocycle in the chosen resolution.
Evaluation at 1 identifies Hom from the constant integer sheaf with global sections in
each degree. This is a chain isomorphism, hence induces the displayed homology isomorphism.
All data are explicit; no arbitrary comparison is chosen from an existence theorem. -/
noncomputable def extSectionsIso (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj G ≅
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj (injectiveResolution G).cochainComplex).homology (q : ℤ) :=
  (injectiveResolution G).extAddEquivCohomologyClass.toAddCommGrpIso ≪≫
    classSectionsIso X (injectiveResolution G).cochainComplex q

end AlgebraicGeometry.SheafPullbackResolution
