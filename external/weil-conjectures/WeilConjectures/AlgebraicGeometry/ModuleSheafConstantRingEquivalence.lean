/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Comparing the two encodings of constant-coefficient module sheaves

Source: Stacks Project, Modules on Sites, Section 18.42 (Tag 093I), opening
paragraph, and Cohomology on Sites, Lemma 21.12.4 (Tag 03FD). The construction
below is the encoding argument needed to apply that lemma.
-/


@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale


-- Work over the ring sheaf appearing in the statement.
private noncomputable abbrev constantRing (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) : Sheaf X.smallEtaleTopology RingCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))

private noncomputable def scalarUnit (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    (Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (constantRing Λ X).obj :=
  Functor.whiskerRight (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

-- Constant-ring module presheaves encode exactly ModuleCat-valued presheaves.
private noncomputable def constantModulePresheaf (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) : (X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤
      PresheafOfModules.{u + 1} ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (scalarUnit Λ X) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective X.smallEtaleTopology
    (Functor.whiskerRight (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (CommRingCat.of Λ))) (forget CommRingCat.{u + 1}))
  infer_instance

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (scalarUnit Λ X) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective X.smallEtaleTopology
    (Functor.whiskerRight (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (CommRingCat.of Λ))) (forget CommRingCat.{u + 1}))
  infer_instance

private noncomputable def constantModuleFullyFaithful
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constantModulePresheaf Λ X).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constantModulePresheaf Λ X).Full := (constantModuleFullyFaithful Λ X).full

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constantModulePresheaf Λ X).Faithful := (constantModuleFullyFaithful Λ X).faithful

private noncomputable def moduleEmbedding (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ constantModulePresheaf Λ X

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleEmbedding Λ X).Full :=
  inferInstanceAs (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    constantModulePresheaf Λ X).Full

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleEmbedding Λ X).Faithful :=
  inferInstanceAs (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    constantModulePresheaf Λ X).Faithful

private noncomputable def moduleExtension (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :=
  moduleEmbedding Λ X ⋙ PresheafOfModules.sheafification.{u + 1} (scalarUnit Λ X)

private noncomputable def moduleExtensionForgetIso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    moduleExtension Λ X ⋙ SheafOfModules.toSheaf (constantRing Λ X) ≅
      sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents (fun F ↦ asIso ((sheafificationAdjunction
    X.smallEtaleTopology AddCommGrpCat.{u + 1}).counit.app
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))
    (fun φ ↦ (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).counit.naturality
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map φ))

-- The module-sheafification unit is invertible on objects already satisfying descent.
private noncomputable instance moduleEmbeddingUnitIsIso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1} (scalarUnit Λ X)).unit.app
      ((moduleEmbedding Λ X).obj F)) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  apply isIso_toSheafify
  exact ((sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property

private noncomputable def moduleEmbeddingUnitIso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    moduleEmbedding Λ X ≅ moduleExtension Λ X ⋙
      (SheafOfModules.forget (constantRing Λ X) ⋙
        PresheafOfModules.restrictScalars (scalarUnit Λ X)) := by
  let η := Functor.whiskerLeft (moduleEmbedding Λ X)
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (scalarUnit Λ X)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    exact moduleEmbeddingUnitIsIso Λ X F
  exact asIso η

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleExtension Λ X).Faithful :=
  Functor.Faithful.of_comp_iso (moduleEmbeddingUnitIso Λ X).symm

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleExtension Λ X).Full :=
  Functor.Full.of_comp_faithful_iso (moduleEmbeddingUnitIso Λ X).symm

private noncomputable def moduleRestrictionObj
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (M : SheafOfModules.{u + 1} (constantRing Λ X)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let P := (PresheafOfModules.restrictScalars (scalarUnit Λ X)).obj M.val
  let F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
    { obj := P.obj
      map f := P.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
  exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp X.smallEtaleTopology F
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩

private noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleExtension Λ X).EssSurj where
  mem_essImage M := by
    refine ⟨moduleRestrictionObj Λ X M, ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1} (scalarUnit Λ X)).counit.app M)

/-- Module-valued étale sheaves are modules over the constant ring sheaf.

Source: Stacks Project, Tag 093I, opening paragraph (constant algebraic structures),
and Tag 03FD (underlying abelian sheaves). The encoding argument is written here.
(blueprint: lem-weil-pbc-module-sheaf-constant-ring-equivalence)

Proof: let R be the sheafification of the constant ring presheaf with value Λ.
For a ModuleCat Λ-valued sheaf F, a section of R is locally represented by elements
of Λ. Multiply such representatives by restrictions of a section of F, then glue.
Local equality of representatives makes this independent of all choices. The
module identities hold locally for Λ and hence globally by separatedness. The
restrictions commute with this action, giving a sheaf of R-modules. A morphism
of Λ-module sheaves respects these local actions and their gluings.
Conversely restrict the R-action along the constant-presheaf sheafification unit
Λ → R(U), for each object U. The module identities and restriction compatibility
give a ModuleCat Λ-valued sheaf, since the additive sheaf is unchanged. R-linear
maps give Λ-linear natural transformations. Restricting the glued action recovers
the original Λ-action. Extending the restricted action recovers the R-action:
locally every scalar comes from Λ, so equality follows by separatedness. These
identities give the unit and counit and their triangle identities. Both functors
retain the same additive sheaf and additive maps; their identity components give
the displayed natural isomorphism of underlying-abelian functors.
All ring and module carriers lie in Type (u+1), while X lies in Scheme.{u}; no
universe lift of X, torsion assumption, or injectivity assumption is required.
For the empty scheme the unique sheaves correspond, and for the zero ring all
module sheaves are zero. The same construction applies to ULift coefficients.
-/
theorem moduleSheaf_constantRing_equivalence
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    : let R : Sheaf X.smallEtaleTopology RingCat.{u + 1} := (sheafCompose X.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
    ∃ (e : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
      SheafOfModules.{u + 1} R),
      Nonempty (e.functor ⋙ SheafOfModules.toSheaf R ≅
        sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  let : (moduleExtension Λ X).IsEquivalence := {}
  exact ⟨(moduleExtension Λ X).asEquivalence, ⟨moduleExtensionForgetIso Λ X⟩⟩

end AlgebraicGeometry
