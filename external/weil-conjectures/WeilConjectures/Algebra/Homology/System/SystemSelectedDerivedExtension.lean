/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.SmoothPurity.NormalizedLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemOrdinarySelectedExtension
public import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation

/-! # Derived extension from a selected subsequence

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
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ)

/-- Selected extension preserves quasi-isomorphisms between componentwise flat-term
K-flat representatives. Source: Zheng 4.1; Stacks 06YT
(blueprint: lem-pur-system-selected-derived-extension).
Proof: exact evaluation takes the original map to a quasi-isomorphism at the first
selected index. Scalar extension preserves that quasi-isomorphism between the K-flat
components. These are the actual evaluations of the extended strict map. Joint
componentwise detection gives the claimed quasi-isomorphism of strict complexes. -/
theorem systemSelected_preserves
    {K L : CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ} (f : K ⟶ L)
    (hK : systemComponentwiseKFlat (selectedSystemRings B r) K)
    (hL : systemComponentwiseKFlat (selectedSystemRings B r) L) (hf : QuasiIso f) :
    QuasiIso (((systemSelectedFunctor S T B r).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (strictRingSystem_quasiIso_iff B _).2
  intro m
  let V := systemEvaluation (selectedSystemRings B r) (systemNextSelected r m)
  have : QuasiIso f := hf
  have hv : QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  change QuasiIso (((systemTensor S B (systemNextSelected_spec r m).1).mapHomologicalComplex
    (.up ℤ)).map ((V.mapHomologicalComplex (.up ℤ)).map f))
  exact (S (B.map (homOfLE (systemNextSelected_spec r m).1).op)).model.preserves _
    (hK _).1 (hL _).1 hv

/-- The selected ordinary adjunction has its normalized total derived adjunction.
Source: Zheng 4.1; Stacks 06XN and 0FND
(blueprint: lem-pur-system-selected-derived-extension).
Proof: the simultaneous strict K-flat resolution resolves the componentwise class.
Selected extension preserves quasi-isomorphisms on this class, so normalized derivation
applies to the ordinary selected adjunction. -/
def systemSelectedDerivedExtension (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    SystemDerivedLeftExtension (systemSubsequence B r)
      (systemComponentwiseKFlat (selectedSystemRings B r)) :=
  (Classical.choice <|
    nonempty_normalizedLeftExtension (systemSubsequence B r) (systemSelectedFunctor S T B r)
      (systemSelectedAdjunction S T B r) (systemComponentwiseKFlat (selectedSystemRings B r))
      (strictRingSystem_kFlatResolution (selectedSystemRings B r))
      (fun f ↦ systemSelected_preserves S T B r f)).toExtension

end SheafOfModules
