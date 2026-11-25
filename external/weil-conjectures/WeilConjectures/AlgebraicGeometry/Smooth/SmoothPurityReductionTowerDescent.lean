/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import all WeilConjectures.AlgebraicGeometry.StrictCoefficientTensor.StrictCoefficientTensorDescent
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization

set_option linter.privateModule false

/-! # Strict reduction in the chosen coefficient-tower presentation

Source: blueprint latest, normalized-towers-reduction, construction paragraph;
Stacks Tags 00YV, 06YS, 06YY, 0G7D.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u c v w

attribute [local instance 21000]
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private def scalarIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (A B : DerivedChangeOfRingsCochainModel φ) : A.E ≅ B.E :=
  NatIso.ofComponents (fun M ↦ eqToIso ((A.obj_eq M).trans (B.obj_eq M).symm)) (by
    intro M N f
    dsimp only [eqToIso, Functor.comp_map]
    rw [A.map_eq, B.map_eq]
    simp only [eqToHom_trans, Category.assoc, eqToHom_trans_assoc])

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

end AlgebraicGeometry.ProEtale
