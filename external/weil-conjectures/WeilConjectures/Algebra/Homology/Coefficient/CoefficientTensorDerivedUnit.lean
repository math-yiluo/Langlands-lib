/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientScalarDerivedAdjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# The derived unit tensor comparison

Source: Stacks Tags 06XN and 03EK, uniqueness of the derived identity tensor.
(blueprint: lem-pur-coefficient-tensor-derived-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ordinary unit tensor comparison induces the universal derived unit comparison,
with its equation on every complex, without a flatness restriction.
Source: Stacks Tags 06XN and 03EK
(blueprint: lem-pur-coefficient-tensor-derived-unit).
Proof: map the ordinary unit comparison to complexes and then to the derived category.
The identity functor is its own left derived functor. Uniqueness of universal left
derived functors gives the isomorphism. The equation for its defining natural
transformation is exactly the stated representative formula. -/
theorem coefficientTensorDerivedUnit
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (n : ℕ) (unit : coefficientTensor (J := J) (O := O) (ell := ell) (Nat.le_refl n) ≅
      𝟭 (coefficientLevelModules (J := J) O ell n)) :
    ∃ i : (scalar (Nat.le_refl n)).derived ≅ 𝟭 _, ∀ P,
      i.hom.app (DerivedCategory.Q.obj P) =
        (scalar (Nat.le_refl n)).counit.app P ≫ DerivedCategory.Q.map
          (((NatIso.mapHomologicalComplex unit (.up ℤ) ≪≫
            CategoryTheory.Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P).hom) := by
  let D := scalar (Nat.le_refl n)
  let W := HomologicalComplex.quasiIso (coefficientLevelModules (J := J) O ell n) (.up ℤ)
  let b := NatIso.mapHomologicalComplex unit (.up ℤ) ≪≫
    CategoryTheory.Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let τ := CategoryTheory.Functor.isoWhiskerRight b DerivedCategory.Q ≪≫
    CategoryTheory.Functor.leftUnitor DerivedCategory.Q
  let := D.isDerived
  let := CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W (𝟭 _)
    (CategoryTheory.Functor.rightUnitor DerivedCategory.Q)
  let i := CategoryTheory.Functor.leftDerivedNatIso D.derived (𝟭 _)
    D.counit (CategoryTheory.Functor.rightUnitor DerivedCategory.Q).hom W τ
  refine ⟨i, ?_⟩
  intro P
  have h := CategoryTheory.Functor.leftDerivedNatTrans_app D.derived (𝟭 _)
    D.counit (CategoryTheory.Functor.rightUnitor DerivedCategory.Q).hom W τ.hom P
  change i.hom.app (DerivedCategory.Q.obj P) ≫ 𝟙 _ =
    D.counit.app P ≫ DerivedCategory.Q.map (b.hom.app P) ≫ 𝟙 _ at h
  change i.hom.app (DerivedCategory.Q.obj P) =
    D.counit.app P ≫ DerivedCategory.Q.map (b.hom.app P)
  simpa only [Category.comp_id] using h

end SheafOfModules
