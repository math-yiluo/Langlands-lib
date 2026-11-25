/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint

/-! The abelian Gabriel--Popescu component of the derived presentation. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- The Gabriel--Popescu abelian presentation, with the large-coproduct hypothesis
needed to extend the small presentation to the displayed module universe.
Source: Stacks Project, Tags 0F5V and 0F5X, with Tag 05NU for the Baer criterion.

(auxiliary; not a blueprint node)

Proof in words: choose a separator G of A and replace its endomorphism ring by
the opposite of the w-small endomorphism ring obtained from local smallness.
For a module M, use the canonical free presentation by coproducts of G and take
the corresponding cokernel in A; this gives F, while Hom(G,-) gives U.  For
w-sized modules the usual Gabriel--Popescu construction proves the adjunction,
the exactness of F, and invertibility of the counit.  The hypothesis that
DerivedCategory A has coproducts indexed by Type (max w vA vH) gives the same
coproducts in A: form the coproduct of the objects concentrated in degree zero,
use vanishing of maps into positive truncations to put it in degree zero, and
identify its zeroth cohomology by the truncation adjunction.  Thus the free
presentation works at the larger size and its counit agrees with the small one.
For an injective I, U(I) is injective on w-small modules; the Baer criterion for
the w-sized ring extends this to all displayed modules.  Adjunction and enough
injectives show that F preserves monomorphisms.  Since a left adjoint is right
exact, F is additive and exact, and the resulting counit is invertible.
-/
theorem gabriel_popescu_abelian_core
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (S : Type w) (rS : Ring S),
      letI := rS
      ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
      letI := hD
      ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
        (adj₀ : F ⊣ U) (addF : F.Additive)
        (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
      let _ := addF
      let _ := limF
      let _ := colimF
      IsIso adj₀.counit := by
  let G := separator.{w} (ShrinkHoms A)
  have hG : IsSeparator G := isSeparator_separator _
  let S : Type w := (End G)ᵐᵒᵖ
  let rS : Ring S := inferInstance
  let : IsGrothendieckAbelian.{max w vH} (ModuleCat.{max w vH} S) :=
    IsGrothendieckAbelian.of_equivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{vH} S ≃+* S)).symm
  let hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S) := inferInstance
  let U : A ⥤ ModuleCat.{max w vH} S :=
    (ShrinkHoms.equivalence.{w} A).functor ⋙ preadditiveCoyonedaObj G ⋙
      ModuleCat.uliftFunctor.{vH, w} S
  have : U.IsRightAdjoint := gabriel_popescu_large_hom_isRightAdjoint G
  have : (preadditiveCoyonedaObj G).Full :=
    IsGrothendieckAbelian.GabrielPopescu.full G hG
  have : (preadditiveCoyonedaObj G).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj G).mp hG
  have : (preadditiveCoyonedaObj G).PreservesInjectiveObjects :=
    IsGrothendieckAbelian.GabrielPopescu.preservesInjectiveObjects G hG
  have : U.Full := inferInstance
  have : U.Faithful := inferInstance
  have : U.PreservesInjectiveObjects := inferInstance
  let F := U.leftAdjoint
  let adj₀ : F ⊣ U := Adjunction.ofIsRightAdjoint U
  have : F.IsLeftAdjoint := adj₀.isLeftAdjoint
  have : F.PreservesMonomorphisms :=
    F.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects adj₀
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have addF : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  have limF : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have colimF : PreservesFiniteColimits F := inferInstance
  exact ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, inferInstance⟩

end CategoryTheory
