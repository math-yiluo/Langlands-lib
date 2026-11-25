/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.Topology.OpenModuleDerivedSections
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Comparison of open derived sections and the canonical truncation tower
Source: Stacks Project, Tags 08BS and 08U1.
(blueprint: lem-sc-open-derived-sections-truncation-tower-comparison). -/

@[expose] public section
universe u wC wV wA
open CategoryTheory Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

private lemma transport_comparison_naturality
    {C D A : Type*} [Category C] [Category D] [Category A]
    (R : C ⥤ D) (H : D ⥤ A) (G : C ⥤ A) (e : R ⋙ H ≅ G)
    {E₁ E₂ : C} {Y₁ Y₂ : D} (a : Y₁ ⟶ Y₂) (f : E₁ ⟶ E₂)
    (c₁ : Y₁ ≅ R.obj E₁) (c₂ : Y₂ ≅ R.obj E₂)
    (h : a ≫ c₂.hom = c₁.hom ≫ R.map f) :
    H.map a ≫ (H.mapIso c₂ ≪≫ e.app E₂).hom =
      (H.mapIso c₁ ≪≫ e.app E₁).hom ≫ G.map f := by
  simp only [Functor.mapIso_hom, Iso.trans_hom, Category.assoc]
  rw [← H.map_comp_assoc, h, H.map_comp_assoc]
  exact congrArg (fun z ↦ H.map c₁.hom ≫ z) (e.hom.naturality f)

private lemma transport_comparison_projection
    {C D A : Type*} [Category C] [Category D] [Category A]
    (R : C ⥤ D) (H : D ⥤ A) (G : C ⥤ A) (e : R ⋙ H ≅ G)
    {E₁ E₂ : C} {Y : D} (a : R.obj E₁ ⟶ Y) (f : E₁ ⟶ E₂)
    (c : Y ≅ R.obj E₂) (h : a ≫ c.hom = R.map f) :
    H.map a ≫ (H.mapIso c ≪≫ e.app E₂).hom =
      (e.app E₁).hom ≫ G.map f := by
  simp only [Functor.mapIso_hom, Iso.trans_hom]
  rw [← H.map_comp_assoc, h]
  exact e.hom.naturality f

private lemma exactFunctor_truncation_comparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (E : DerivedCategory C) :
    let R := F.mapDerivedCategory
    let t := DerivedCategory.TStructure.t (C := C)
    let s := DerivedCategory.TStructure.t (C := D)
    ∃ c : ∀ b : ℤ, (s.truncGE b).obj (R.obj E) ≅ R.obj ((t.truncGE b).obj E),
      (∀ b, (s.truncGEπ b).app (R.obj E) ≫ (c b).hom =
        R.map ((t.truncGEπ b).app E)) ∧
      (∀ b₁ b₂ (h : b₁ ≤ b₂),
        (s.natTransTruncGEOfLE b₁ b₂ h).app (R.obj E) ≫ (c b₂).hom =
          (c b₁).hom ≫ R.map ((t.natTransTruncGEOfLE b₁ b₂ h).app E)) := by
  let R := F.mapDerivedCategory
  let t := DerivedCategory.TStructure.t (C := C)
  let s := DerivedCategory.TStructure.t (C := D)
  let c (b : ℤ) := (F.mapDerivedCategoryTruncGEIso b).symm.app E
  have hc (b : ℤ) : (s.truncGEπ b).app (R.obj E) ≫ (c b).hom =
      R.map ((t.truncGEπ b).app E) := by
    have : s.IsGE ((t.truncGE b ⋙ R).obj E) b :=
      F.isGE_mapDerivedCategory_obj ((t.truncGE b).obj E) b
    change _ ≫ s.descTruncGE _ b = _
    exact s.π_descTruncGE _ _
  refine ⟨c, hc, ?_⟩
  intro b₁ b₂ h
  have : s.IsGE ((t.truncGE b₂ ⋙ R).obj E) b₂ :=
    F.isGE_mapDerivedCategory_obj ((t.truncGE b₂).obj E) b₂
  have : s.IsGE ((t.truncGE b₂ ⋙ R).obj E) b₁ := s.isGE_of_ge _ _ b₂ h
  apply s.from_truncGE_obj_ext (Y := (t.truncGE b₂ ⋙ R).obj E)
  rw [← Category.assoc, s.π_natTransTruncGEOfLE_app, hc,
    ← Category.assoc, hc, ← R.map_comp, t.π_natTransTruncGEOfLE_app]

private lemma exactFunctor_truncationTower_comparison
    {C D A : Type*} [Category C] [Category D] [Category A] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (H : DerivedCategory D ⥤ A)
    (G : DerivedCategory C ⥤ A) (eD : F.mapDerivedCategory ⋙ H ≅ G)
    (E : DerivedCategory C) :
    let R := F.mapDerivedCategory
    let t := DerivedCategory.TStructure.t (C := C)
    let s := DerivedCategory.TStructure.t (C := D)
    ∃ (e : H.obj (R.obj E) ≅ G.obj E)
      (en : ∀ n : ℕ, H.obj ((s.truncGE (-(n : ℤ))).obj (R.obj E)) ≅
        G.obj ((t.truncGE (-(n : ℤ))).obj E)),
      (∀ n : ℕ, H.map ((s.truncGEπ (-(n : ℤ))).app (R.obj E)) ≫ (en n).hom =
        e.hom ≫ G.map ((t.truncGEπ (-(n : ℤ))).app E)) ∧
      (∀ n : ℕ, H.map
        ((s.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app (R.obj E)) ≫
          (en n).hom = (en (n + 1)).hom ≫ G.map
            ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)) := by
  let R := F.mapDerivedCategory
  let t := DerivedCategory.TStructure.t (C := C)
  let s := DerivedCategory.TStructure.t (C := D)
  obtain ⟨c, hc, ht⟩ := exactFunctor_truncation_comparison F E
  let en (n : ℕ) := H.mapIso (c (-(n : ℤ))) ≪≫ eD.app ((t.truncGE (-(n : ℤ))).obj E)
  refine ⟨eD.app E, en, ?_, ?_⟩
  · intro n
    exact transport_comparison_projection R H G eD
      ((s.truncGEπ (-(n : ℤ))).app (R.obj E)) ((t.truncGEπ (-(n : ℤ))).app E)
      (c (-(n : ℤ))) (hc _)
  · intro n
    exact transport_comparison_naturality R H G eD
      ((s.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (by omega)).app (R.obj E))
      ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)
      (c (-((n + 1 : ℕ) : ℤ))) (c (-(n : ℤ))) (ht _ _ (by omega))

/-- Derived evaluation on an open agrees with sections after exact restriction,
including the canonical lower-truncation projection and transition maps.
Source: Stacks Project, Tag 08BS, and the uniqueness of standard truncations.
(blueprint: lem-sc-open-derived-sections-truncation-tower-comparison).

Proof: Restriction to V is exact and preserves K-injective complexes by its exact
extension-by-zero left adjoint; transport this through Modules.overEquiv V. On a
K-injective representative, both functors are termwise abelian sections on V,
so the defining derived units give a natural isomorphism on every object E.
Exact restriction is t-exact: it commutes with homology and preserves both
standard cohomological support conditions. Apply restriction to the truncation
triangle. Its vertices have the required support, hence uniqueness of truncations
gives restriction(truncGE b E) ≅ truncGE b(restriction E), respecting truncGEπ.
For b ≤ c the two resulting transition maps coincide by the universal property
of truncGE b, since their composites with its projection agree. Apply derived
sections to these isomorphisms and compose with the preceding natural comparison.
Naturality gives the two displayed squares. This works on empty opens and for
unbounded E, independently of any homology acyclicity assumption. -/
theorem openDerivedSections_truncationTower_comparison
    (X : Scheme.{u}) (V : X.Opens)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    let H := RingedSpace.openModuleSections V.toScheme.toRingedSpace ⊤
    let R := (schemeOpenRestriction X V).mapDerivedCategory
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let s := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    ∃ (e : H.rightDerivedFunctor.obj (R.obj E) ≅ G.rightDerivedFunctor.obj E)
      (en : ∀ n : ℕ, H.rightDerivedFunctor.obj ((s.truncGE (-(n : ℤ))).obj (R.obj E)) ≅
        G.rightDerivedFunctor.obj ((t.truncGE (-(n : ℤ))).obj E)),
      (∀ n : ℕ, H.rightDerivedFunctor.map ((s.truncGEπ (-(n : ℤ))).app (R.obj E)) ≫
        (en n).hom = e.hom ≫ G.rightDerivedFunctor.map ((t.truncGEπ (-(n : ℤ))).app E)) ∧
      (∀ n : ℕ, H.rightDerivedFunctor.map
        ((s.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app (R.obj E)) ≫
          (en n).hom = (en (n + 1)).hom ≫ G.rightDerivedFunctor.map
            ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)) := by
  dsimp only
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let G := S ⋙ forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
  let H := RingedSpace.openModuleSections V.toScheme.toRingedSpace ⊤
  let F := schemeOpenRestriction X V
  let R := F.mapDerivedCategory
  let : Functor.PreservesKInjectiveComplexes
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V) :=
    ⟨fun I _ ↦ kInjective_of_restrict_open X.toRingedSpace V I⟩
  let : (Scheme.Modules.overEquiv V).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : F.PreservesKInjectiveComplexes := by
    dsimp [F, schemeOpenRestriction]
    apply Functor.preservesKInjectiveComplexes_comp
  have under' : Scheme.Modules.restrictFunctor V.ι ⋙ H ≅ G := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · change (Scheme.Modules.presheaf (Scheme.Modules.restrict M V.ι)).obj (op ⊤) ≅
        (Scheme.Modules.presheaf M).obj (op V)
      exact (Scheme.Modules.presheaf M).mapIso (eqToIso V.ι_image_top.symm).op
    · intro M N f
      change (Scheme.Modules.Hom.mapPresheaf f).app (op (V.ι ''ᵁ ⊤)) ≫
          (Scheme.Modules.presheaf N).map (eqToHom V.ι_image_top.symm).op =
        (Scheme.Modules.presheaf M).map (eqToHom V.ι_image_top.symm).op ≫
          (Scheme.Modules.Hom.mapPresheaf f).app (op V)
      exact ((Scheme.Modules.Hom.mapPresheaf f).naturality _).symm
  let under : F ⋙ H ≅ G :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv V) H ≪≫ under'
  let eD : R ⋙ H.rightDerivedFunctor ≅ G.rightDerivedFunctor :=
    Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm
      H.rightDerivedFunctor ≪≫ Functor.rightDerivedFunctorCompIso' F H under
  exact exactFunctor_truncationTower_comparison F H.rightDerivedFunctor G.rightDerivedFunctor eD E

end AlgebraicGeometry
