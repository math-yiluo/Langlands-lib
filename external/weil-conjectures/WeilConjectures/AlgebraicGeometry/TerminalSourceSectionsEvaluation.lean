/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension

/-! # Evaluation of the fixed terminal-source comparison
Source: Stacks Project, Tags 06XR and 01F7.
(blueprint: new-terminal-source-sections-evaluation)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

/-- Evaluation through the terminal-source comparison agrees with the integer generator.
Source: Stacks Project, Tag 06XR; the constant-sheaf and free-abelian adjunctions.
(blueprint: new-terminal-source-sections-evaluation)

Proof: The free singleton generator maps to the integer 1. Expand the two
adjunctions, commute the singleton isomorphism through sheafification using
naturality of its unit, and evaluate on that generator. -/
theorem terminal_source_sections_evaluation (X : Scheme.{u})
    (N : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ N) :
    (sectionsIso (Opens.grothendieckTopology X) ⊤).hom.app N
      ((terminalSourceIso X).hom ≫ a) =
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homAddEquiv _ N a) := by
  change sectionsEquiv _ ⊤ N ((terminalSourceIso X).hom ≫ a) = _
  dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_unit]
  change (a.hom.app (op ⊤))
      (((toSheafify _ _).app (op ⊤) ≫ (terminalSourceIso X).hom.hom.app (op ⊤))
        (FreeAbelianGroup.of (𝟙 (⊤ : X.Opens)))) = _
  let e : yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free ≅
      (Functor.const X.Opensᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : X.Opens)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro z
        simp [FreeAbelianGroup.uniqueEquiv])
  have hn := congr_app (toSheafify_naturality (Opens.grothendieckTopology X) e.hom)
    (op (⊤ : X.Opens))
  change e.hom.app (op ⊤) ≫ (toSheafify _ _).app (op ⊤) =
    (toSheafify _ _).app (op ⊤) ≫ (terminalSourceIso X).hom.hom.app (op ⊤) at hn
  rw [← hn]
  have he : e.hom.app (op ⊤) (FreeAbelianGroup.of (𝟙 (⊤ : X.Opens))) =
      (ULift.up (1 : ℤ)) := by
    simp [e, FreeAbelianGroup.uniqueEquiv]
    rfl
  simp only [ConcreteCategory.comp_apply, he]
  change _ = ((constantSheafAdj _ _ isTerminalTop).homEquiv _ N a) (ULift.up 1)
  rw [Adjunction.homEquiv_unit]
  rfl

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
