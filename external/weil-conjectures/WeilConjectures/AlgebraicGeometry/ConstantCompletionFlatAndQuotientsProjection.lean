/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
/-! Projection quotient component of constant coefficient completion.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node).
(auxiliary; not a blueprint node)
The sectionwise adic algebra limit argument identifies each original completion
projection with the quotient by the extended power of the coefficient ideal. -/
@[expose] public noncomputable section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
theorem flat_and_quotients_projection (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∀ (n : ℕ) (U : C),
      Function.Surjective ((projection J A I n).hom.app (op U)) ∧
      RingHom.ker ((projection J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (algebraSection (coefficientMap J A I) a).val (op U))) := by
  let S := finiteSystemUnder J A I
  letI : ∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1)) (adicTerm J A S n U) :=
    finiteSystemModule J A I
  have hprops := finiteSystem_properties J A I
  letI : ∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1))
      (adicTerm J A S n U) := hprops.1
  obtain ⟨e, he, _, _⟩ :=
    (sectionwise_adic_algebra_limit.{u, u} J A I S hprops.2.1 hprops.2.2.1 hprops.2.2.2).2.2.2.2.2
  intro n U
  let X := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)
  letI : CreatesLimitsOfSize (Under.forget X) := Under.createsLimitsOfSize
  letI : HasLimit (S ⋙ Under.forget X) := by
    change HasLimit (finiteSystem J A I)
    infer_instance
  letI : CreatesLimit S (Under.forget X) := by
    exact CreatesLimitsOfShape.CreatesLimit
  letI : PreservesLimit S (Under.forget X) :=
    preservesLimit_of_createsLimit_and_hasLimit S (Under.forget X)
  let L := preservesLimitIso (Under.forget X) S
  have hsurj : Function.Surjective ((projection J A I n).hom.app (op U)) := by
    intro y
    obtain ⟨z, hz⟩ := (e n (op U)).surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨(L.hom.hom.app (op U)) b, ?_⟩
    have hp := congrArg (fun f ↦ f.hom.app (op U))
      (preservesLimitIso_hom_π (Under.forget X) S (op n))
    have hp' := ConcreteCategory.congr_hom hp b
    have hpL :
        (projection J A I n).hom.app (op U) ((L.hom.hom.app (op U)) b) =
          (ConcreteCategory.hom (((Under.forget X).map (limit.π S (op n))).hom.app
            (op U))) b := by
      change (projection J A I n).hom.app (op U) ((L.hom.hom.app (op U)) b) =
        (ConcreteCategory.hom (((Under.forget X).map (limit.π S (op n))).hom.app
          (op U))) b at hp'
      exact hp'
    have hpR :
        (ConcreteCategory.hom (((Under.forget X).map (limit.π S (op n))).hom.app
          (op U))) b = adicProjection J A S n (op U) b := by
      change _ = ((adicAlgebraSections J A (op U)).map (limit.π S (op n))).hom b
      rfl
    have hp'' := hpL.trans hpR
    exact hp''.trans (he n (op U) b).symm |>.trans hz
  exact ⟨hsurj, flat_and_quotients_projection_kernel J A I n U⟩
end CategoryTheory.ConstantCompletion
