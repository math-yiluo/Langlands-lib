/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
public import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
/-! Module structures for the finite constant completion tower.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node).
The quotient coefficient sections carry their canonical module structures over the
corresponding quotient rings. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
def finiteSystemUnder (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)) :=
  Under.lift (finiteSystem J A I) (quotientCone J A I).π

end CategoryTheory.ConstantCompletion
