/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic

/-! # Normalized representative of singleton coefficient change

Source: Stacks 0FND, 09T5 and 0D6D; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)
  (A : SystemScalarModel (singletonSequenceRingMap a))

/-- The specified derived conjugate is represented by the ordinary singleton
coefficient comparison, with the actual universal comparison maps.
Source: Stacks, Derived Categories, lemmas pre-derived-adjoint-functors (0FND) and
derived-adjoint-functors (09T5), and Cohomology on Sites, 0D6D; the singleton
calculation is the argument in the parent node, Steps 7--8.
(blueprint: lem-pur-system-singleton-scalar-representative)

Proof: transport the normalized singleton transpose through the exact sequence
 equivalence and its derived compositor. Compose this transpose with the normalized
scalar transpose, on each side of the evaluation/restriction square. On complexes,
the ordinary uniqueness map transposes to the target composite unit in each degree.
The right square is identity on sections and its derived square is its canonical
exact-functor localization, so inverse factorization maps satisfy the same square.
Apply normalizedAdjunction_composition to the two pairs of adjunctions and then
normalizedAdjunction_uniqueness to these compatible right comparisons. Its conclusion
is exactly the displayed equality after identifying the componentwise cochain map
of the ordinary uniqueness isomorphism. This argument uses arbitrary complexes:
K-flatness is needed only to invert the two universal comparison maps. -/
theorem singletonScalarDerivedIso_rep (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) :
      (singletonScalarDerivedIso S T a A n).hom.app (DerivedCategory.Q.obj P) ≫
          singletonScalarTargetComparison S T a n P =
        singletonScalarSourceComparison S T a A n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (singletonScalarOrdinaryIso S T a A n)
            (.up ℤ)).hom.app P) := by sorry

end SheafOfModules
