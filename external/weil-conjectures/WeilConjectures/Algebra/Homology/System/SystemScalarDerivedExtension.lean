/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic

/-! # Scalar models as normalized derived adjunctions

Source: Stacks 06YY and 0FND.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- A scalar model already has all normalized extension data. Its resolving class
is the class of K-flat complexes. Source: Stacks 06YY and 0FND
(blueprint: lem-pur-system-scalar-derived-extension). -/
def systemScalarModelExtension {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (A : SystemScalarModel φ) :
    SystemDerivedLeftExtension
      (restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ))
      (CochainComplex.IsKFlatIndependentCoefficients (R := R)) where
  ordinary := A.model.E
  ordinaryAdj := A.ordinaryAdj
  derived := A.model.T
  comparison := A.model.ε
  universal := A.model.universal
  pointwise := A.model.pointwise
  computes := A.model.computes
  shift := Classical.choose A.model.triangulated
  triangulated := Classical.choose_spec A.model.triangulated
  adjunction := A.adjunction
  transpose := A.transpose

end SheafOfModules
