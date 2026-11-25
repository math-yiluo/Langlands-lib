/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact

/-! # The integral coefficient localization telescope on a scheme -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The leg `p_X^*(ℓ⁻ᵏ φ) : 𝒪_{E,X} ⟶ E_X` as a map of `𝒪_{E,X}`-modules; it is linear by base
`Mod.linear_of_isColimit` and the commutativity of `E_X`. -/
private noncomputable def coeffLeg (X : Scheme.{u}) (k : ℕ) :
    Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      (Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)) :=
  Mod.Hom.mk' (coefficientMapInvPow ℓ E X k) (by
    have hlin := Mod.linear_of_isColimit _ (isColimitCoefficientMapSmulSequenceCocone ℓ E X)
      (coefficientMapInvPow_zero ℓ E X) k
    change μ ≫ coefficientMapInvPow ℓ E X k = _ ◁ coefficientMapInvPow ℓ E X k ≫
      coefficientMap (integralScalarMap ℓ E) X ▷ _ ≫ μ
    rw [← IsCommMonObj.mul_comm (condensedRingObj (Profinite.continuousMapRingObj E) X),
      BraidedCategory.braiding_naturality_left_assoc,
      BraidedCategory.braiding_naturality_right_assoc, hlin, ← Category.assoc,
      IsCommMonObj.mul_comm])

private lemma nsmul_coeffLeg_succ (X : Scheme.{u}) (k : ℕ) :
    ℓ • coeffLeg ℓ E X (k + 1) = coeffLeg ℓ E X k :=
  (Mod.forget _).map_injective (by
    rw [Functor.map_nsmul]
    exact nsmul_coefficientMapInvPow_succ ℓ E X k)

/-- The colimit `E_X = colim(𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯)` of base
`Mod.isColimitSmulSequenceCoconeMap` (`isColimitCoefficientMapSmulSequenceCocone`), lifted to
`𝒪_{E,X}`-modules: the forgetful functor reflects it. -/
private noncomputable def isColimitCoeffLegCocone (X : Scheme.{u}) :
    IsColimit (Mod.smulSequenceCocone ℓ (coeffLeg ℓ E X) (nsmul_coeffLeg_succ ℓ E X)) := by
  let F := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  refine isColimitOfReflects F ((IsColimit.precomposeHomEquiv
    (Mod.smulSequenceCompIso F (Mod.regular _) ℓ) _).symm
      (isColimitCoefficientMapSmulSequenceCocone ℓ E X) |>.ofIsoColimit ?_)
  exact Cocone.ext (Iso.refl _) fun k ↦ by
    simp [Mod.smulSequenceCompIso, F, coeffLeg]

/-- The restricted rational coefficient module is the localization telescope of the
regular integral module, with stage `n` dividing the canonical inclusion by `ℓ ^ n`.
Source: Bhatt--Scholze, Section 6.8 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)

Proof. The diagram is base `Mod.smulSequence` of the regular integral module and the nth
leg is `p_X^*(ℓ⁻ⁿ φ)`, linear by base `Mod.linear_of_isColimit`. On underlying abelian sheaves
this is the colimit `isColimitCoefficientMapSmulSequenceCocone` (base
`Mod.isColimitSmulSequenceCoconeMap`), which the forgetful functor reflects. The leg relation
is base `Mod.pow_sub_nsmul_eq`, and the zeroth leg is `p_X^* φ`. -/
theorem integralCoefficient_localization_telescope (X : Scheme.{u}) :
    ∃ (D : ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) (c : Cocone D)
      (e : ∀ n, D.obj n ≅ Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
      (p : c.pt ≅ (Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X))),
      Nonempty (IsColimit c) ∧
      (∀ n : ℕ, ℓ ^ n • ((e n).inv ≫ c.ι.app n) = (e 0).inv ≫ c.ι.app 0) ∧
      (((e 0).inv ≫ c.ι.app 0 ≫ p.hom).hom =
        coefficientMap (integralScalarMap ℓ E) X) := by
  refine ⟨Mod.smulSequence _ ℓ, Mod.smulSequenceCocone ℓ (coeffLeg ℓ E X)
    (nsmul_coeffLeg_succ ℓ E X), fun _ ↦ Iso.refl _, Iso.refl _,
    ⟨isColimitCoeffLegCocone ℓ E X⟩, fun n ↦ ?_, coefficientMapInvPow_zero ℓ E X⟩
  simpa only [Iso.refl_inv, Category.id_comp, Nat.sub_zero] using
    Mod.pow_sub_nsmul_eq (nsmul_coeffLeg_succ ℓ E X) (Nat.zero_le n)

end AlgebraicGeometry.ProEtale.CondensedRing
