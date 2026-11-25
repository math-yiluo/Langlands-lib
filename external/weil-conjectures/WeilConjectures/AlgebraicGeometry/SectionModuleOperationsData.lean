/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
/-! # Existing section-module operations and pure-tensor data

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03D6, 03D7,
03DI, 03DJ, 03EK and 0GMW (auxiliary; not a blueprint node).

These transparent aliases expose the existing constructions in the two imported
comparison modules. They introduce no replacement functors, maps, or tensors.
The comparison theorems about these data remain proof dependencies of consumers.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing pulled-back coefficient ring, in section-ring form.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
abbrev ring (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)

/-- The ringed-site module category, retaining the site's actual Hom universe.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
abbrev modules (X : Scheme.{u}) :=
  SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X))

/-- The specified sectionwise equivalence; no new module encoding is introduced.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
@[reducible] def equivalence (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)

/-- The existing section-ring map induced by the adjunct coefficient map.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  InternalModuleOperations.coefficientMap Λ f

/-- The existing ringed direct image with its fixed coefficient map.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) : modules Λ X ⥤ modules Λ Y :=
  InternalModuleOperations.lowerStar Λ f

/-- The existing tensor-formula ringed inverse image.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : modules Λ Y ⥤ modules Λ X :=
  InternalModuleOperations.upperStar Λ f

/-- The existing ringed module adjunction with its specified Hom bijection.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback Λ f ⊣ pushforward Λ f :=
  InternalModuleOperations.adjunction Λ f

/-- Internal modules over the specified coefficient object.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
abbrev internalModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The existing direct-image comparison, identity on all sections.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev pushComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  InternalModuleOperations.lowerComparison Λ f

/-- The existing adjunction-normalized inverse-image comparison.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev pullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  InternalModuleOperations.upperComparison Λ f

/-- The existing sectionwise direct-image compositor.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev pushforwardComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  InternalModuleOperations.lowerComp Λ f g

/-- The existing inverse-image compositor, mate of geometric direct-image pasting.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev pullbackComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback Λ (f ≫ g) ≅ pullback Λ g ⋙ pullback Λ f :=
  InternalModuleOperations.upperComp Λ f g

/-- The existing local pure tensor in the internal relative-tensor coequalizer.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev internalPureTensor (X : Scheme.{u}) (M N : internalModules Λ X) (U : X.ProEtᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) : (M ⊗ N).X.obj.obj U :=
  InternalAbelianSheafModule.comparison_internalTmul.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N U x y

/-- The existing local pure tensor in the sheafified section-module tensor.
Source: Stacks 03EK and 0GMW (auxiliary; not a blueprint node). -/
abbrev sectionPureTensor (X : Scheme.{u}) (M N : modules Λ X) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (M ⊗ N).val.obj U :=
  InternalAbelianSheafModule.comparison_sectionTmul.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N U x y

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
