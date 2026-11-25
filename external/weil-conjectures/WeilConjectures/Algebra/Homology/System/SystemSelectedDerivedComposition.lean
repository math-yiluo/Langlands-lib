/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Composition of derived subsequence extensions

Source: Zheng, Construction 4.1; Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r s : ℕ ↪o ℕ)

/-- Composite extension is the canonical identification of the two left adjoints
to composite restriction. Source: Zheng 4.1; Stacks 0FND
(blueprint: lem-pur-system-selected-derived-composition). -/
def systemSelectedDerivedComposition :
    (systemSelectedDerivedExtension (selectedSystemRings B r) s S T).derived ⋙
      (systemSelectedDerivedExtension B r S T).derived ≅
        (systemSelectedDerivedExtension B (s.trans r) S T).derived :=
  (((systemSelectedDerivedExtension (selectedSystemRings B r) s S T).adjunction.comp
      (systemSelectedDerivedExtension B r S T).adjunction).ofNatIsoRight
        (systemDerivedSubsequenceComposition B r s)).leftAdjointUniq
          (systemSelectedDerivedExtension B (s.trans r) S T).adjunction

/-- Composition of extensions preserves every actual transpose, including its
restriction compositor. Source: Stacks 0FND
(blueprint: lem-pur-system-selected-derived-composition).
Proof: the inverse adjoint-uniqueness comparison is the forward comparison for the
reversed adjunction pair. Its Hom normalization identifies the transpose with the
composite adjunction. Expand the latter and its right-functor transport. -/
theorem systemSelectedDerivedComposition_mate
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B (s.trans r))))
    (M : DerivedCategory (StrictRingSystem B))
    (f : (systemSelectedDerivedExtension B r S T).derived.obj
      ((systemSelectedDerivedExtension (selectedSystemRings B r) s S T).derived.obj P) ⟶ M) :
    (systemSelectedDerivedExtension B (s.trans r) S T).adjunction.homEquiv P M
      ((systemSelectedDerivedComposition S T B r s).inv.app P ≫ f) =
    (systemSelectedDerivedExtension (selectedSystemRings B r) s S T).adjunction.homEquiv P
      ((derivedSystemSubsequence B r).obj M)
      ((systemSelectedDerivedExtension B r S T).adjunction.homEquiv _ M f) ≫
      (systemDerivedSubsequenceComposition B r s).hom.app M := by
  dsimp only [systemSelectedDerivedComposition]
  rw [Adjunction.leftAdjointUniq_inv_app, leftAdjointUniq_homEquiv_comp,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

end SheafOfModules
