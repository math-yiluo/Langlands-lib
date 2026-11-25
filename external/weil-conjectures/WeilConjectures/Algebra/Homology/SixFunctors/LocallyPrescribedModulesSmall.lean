/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Smallness of module sheaves with prescribed local models

Source: Stacks Project, Sites, Tag 04TQ and Modules on Sites, Tag 03EM; the
Essentially small paragraph of the current blueprint's Brown hypotheses proof
(blueprint: lem-sfb-locally-prescribed-modules-small).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

private theorem essentiallySmall_embeds
    {A : Type*} [Category* A] {D : Type*} [Category* D]
    [LocallySmall.{u} D] [WellPowered.{u} D]
    (F : A ⥤ D) (hF : F.FullyFaithful) (Q : D) :
    ObjectProperty.EssentiallySmall.{u}
      (fun X ↦ ∃ f : F.obj X ⟶ Q, Mono f) := by
  classical
  let S := {s : Subobject Q // ∃ X : A, Nonempty (F.obj X ≅ (s : D))}
  let repr : S → A := fun s ↦ s.property.choose
  have hre (s : S) : Nonempty (F.obj (repr s) ≅ (s.val : D)) :=
    s.property.choose_spec
  refine ⟨ObjectProperty.ofObj repr, inferInstance, ?_⟩
  intro X ⟨f, hf⟩
  let s : S := ⟨Subobject.mk f, X, ⟨(Subobject.underlyingIso f).symm⟩⟩
  exact ⟨repr s, ⟨s⟩,
    ⟨hF.preimageIso ((Subobject.underlyingIso f).symm ≪≫ (hre s).some.symm)⟩⟩

end SheafOfModules
