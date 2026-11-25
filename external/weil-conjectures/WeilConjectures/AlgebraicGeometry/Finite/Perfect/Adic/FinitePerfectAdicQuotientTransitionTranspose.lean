/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientStrictSquare
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnit
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnique
import WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso
import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso
import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso

/-! # Transposes of the ordinary quotient arrows

The transpose of the ordinary quotient arrow under extension of scalars along the consecutive
quotient map `q : A_(n+1) → A_n` is invertible. The arrow factors as the image under the chart
coordinates of the ring-level quotient transition `R_(n+1) ⊗ N ⟶ R_n ⊗ N`, followed by the
strict square identifying the two scalar restrictions. The transpose is accordingly the mate of
this square followed by the chart image of the ring-level transpose; the latter is the
comparison of the left adjoints of the restriction along `R → R_n`, and the mate is invertible
since its iterated mate along the chart adjunctions is.

Source: Stacks Project, Tags 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The transpose of a consecutive quotient arrow under extension of scalars along the
consecutive quotient map is invertible.
Source: Stacks Project, Tags 06YY and 09C6.

Proof: by uniqueness the arrow is the explicit one, which is the chart image of the ring-level
transition `R_(n+1) ⊗ N ⟶ R_n ⊗ N` followed by the strict square of scalar restrictions.
Its transpose is the mate of that square followed by the chart image of the ring-level
transpose. The ring-level transpose is the comparison of two left adjoints of restriction
along `R → R_n`, as both units send `x` to `1 ⊗ x`. The iterated mate of the square along the
chart adjunctions is the mate along the constant-scalar equivalences, which is invertible,
pasted with the mate along `j^* ⊣ j_*`, which is the identity; hence the mate is invertible. -/
theorem finitePerfectAdicQuotientTransition_transpose_isIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (V : X.Etale) (n : ℕ)
    (δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (hδ : FinitePerfectAdicQuotientTransition X d φ V n δ) (N : CompletedAdicModules X d) :
    IsIso (((ProEtale.sheafExtendScalarsAdjunction
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        V.left).homEquiv _ _).symm (δ.app N)) := by
  obtain rfl := finitePerfectAdicQuotientTransition_unique X d φ V n δ
    (finitePerfectAdicQuotientStrictTransition X d φ hcompat V n) hδ
    (fun N _ b x ↦ completedAdicChangeQuotientTransition_tensor X d n N _ b x)
  have := finitePerfectAdicFixedScalar_isEquivalence X d φ hφ n
  have := finitePerfectAdicFixedScalar_isEquivalence X d φ hφ (n + 1)
  let adjΘ₀ := (finitePerfectAdicFixedScalar X d φ n).asEquivalence.toAdjunction
  let adjΘ₁ := (finitePerfectAdicFixedScalar X d φ (n + 1)).asEquivalence.toAdjunction
  let adjj₀ := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.hom inferInstance
  let adjj₁ := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) V.hom inferInstance
  let adjR := pbcScalarAdjunction (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
  let adjq := ProEtale.sheafExtendScalarsAdjunction
    (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) V.left
  have hΘ : IsIso (mateEquiv adjΘ₀ adjΘ₁
      (finitePerfectAdicFixedScalarStepIso X d φ hcompat n).hom) := by
    have (Y : _) : IsIso ((mateEquiv adjΘ₀ adjΘ₁
        (finitePerfectAdicFixedScalarStepIso X d φ hcompat n).hom).app Y) :=
      isIso_mateEquiv_app_of_isIso_map_counit adjΘ₀ adjΘ₁ _ Y inferInstance
    exact NatIso.isIso_of_isIso_app _
  have hmate : IsIso (mateEquiv (adjΘ₀.comp adjj₀) (adjΘ₁.comp adjj₁)
      (finitePerfectAdicQuotientStrictSquare X d φ hcompat V n)) := by
    rw [finitePerfectAdicQuotientStrictSquare, mateEquiv_hcomp]
    exact TwoSquare.isIso_hComp _ _
  have hμ := isIso_mateEquiv_symm_of_isIso_mateEquiv adjR adjq (adjΘ₁.comp adjj₁)
    (adjΘ₀.comp adjj₀) (finitePerfectAdicQuotientStrictSquare X d φ hcompat V n)
  have hτ := Adjunction.isIso_homEquiv_symm_of_unit_comp
    (pbcScalarAdjunction (completedAdicCommProjection X d (n + 1))) adjR
    (pbcScalarAdjunction (completedAdicCommProjection X d n))
    (pbcRestrictComp (completedAdicCommProjection X d (n + 1))
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
      (completedAdicCommProjection X d n)
      (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))) N
    ((completedAdicChangeQuotientTransition X d n).app N)
    (completedAdicChangeQuotientTransition_unit X d n N)
  have key := Adjunction.homEquiv_symm_map_comp_app adjR adjq
    (finitePerfectAdicQuotientStrictSquare X d φ hcompat V n)
    ((completedAdicChangeQuotientTransition X d n).app N)
  have hiso : IsIso (((mateEquiv adjR adjq).symm
      (finitePerfectAdicQuotientStrictSquare X d φ hcompat V n)).app
        ((completedAdicChange X (completedAdicCommProjection X d (n + 1))).obj N) ≫
      (finitePerfectAdicFixedScalar X d φ n ⋙ ProEtale.localizationRestriction
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.hom inferInstance).map
        ((adjR.homEquiv _ _).symm ((completedAdicChangeQuotientTransition X d n).app N))) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _)
      (@Functor.map_isIso _ _ _ _ _ _ _ _ hτ)
  rw [← key] at hiso
  rw [finitePerfectAdicQuotientStrictTransition_app]
  exact hiso

end AlgebraicGeometry.Scheme
