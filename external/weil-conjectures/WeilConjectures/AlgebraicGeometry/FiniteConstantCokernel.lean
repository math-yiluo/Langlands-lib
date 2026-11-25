/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentColimit

/-! # Cokernels of finite constant pro-etale module sheaves -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
private lemma constant_finite_etale (X : Scheme.{u})
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsFiniteLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) where
  toIsLocallyConstantSheaf := by
    have : ∀ (U : X.Etale) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
        (Over.forget U).op.HasPointwiseRightKanExtension P := by
      intro U P Y
      have : EssentiallySmall.{u + 1} (StructuredArrow Y (Over.forget U).op) :=
        essentiallySmallSelf.{0} _
      have : HasLimitsOfShape (StructuredArrow Y (Over.forget U).op)
          (ModuleCat.{u + 1} Λ) := hasLimitsOfShape_of_essentiallySmall.{u + 1} _ _
      exact HasLimitsOfShape.has_limit _
    exact (Sheaf.isConstant_of_iso _ (Iso.refl _)).isLocallyConstantSheaf
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    have : LocallySmall.{u} X.Etale := locallySmall_self _
    have : Module.Finite Λ M := Module.Finite.of_finite
    exact ((ModuleCat.isFinitelyGenerated_iff M).2 this).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm⟩

omit [Finite Λ] in
/-- A cokernel between constant finite module sheaves is finite locally constant.
Source: Bhatt--Scholze, Lemma 5.4.1; the constant-sheaf morphism and cokernel
argument in blueprint lemma-constructible-hom-constant-locally.
(auxiliary; not a blueprint node)

Proof. Lift the morphism to etale constant sheaves using full faithfulness of
comparison pullback. Their cokernel is finite locally constant by the etale
constant-morphism lemma. Exact comparison pullback identifies its image with
the given cokernel and sends its finite constant trivializations to pro-etale
trivializations. This includes the zero ring and the empty scheme. -/
theorem isFiniteLocallyConstant_cokernel_constant (X : Scheme.{u})
    (M N : ModuleCat.{u + 1} Λ) [Finite M] [Finite N]
    (f : (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj M ⟶
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj N) :
    IsFiniteLocallyConstant Λ (cokernel f) := by
  let V := ν^*(X)[ModuleCat.{u + 1} Λ]
  let CM := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let CN := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
  let eM := (comparisonUpperStarConstantSheafIso Λ X).app M
  let eN := (comparisonUpperStarConstantSheafIso Λ X).app N
  let g : CM ⟶ CN := V.preimage (eM.hom ≫ f ≫ eN.inv)
  have : IsFiniteLocallyConstantSheaf CM := constant_finite_etale X M
  have : IsFiniteLocallyConstantSheaf CN := constant_finite_etale X N
  have : IsFiniteLocallyConstantSheaf (cokernel g) :=
    IsFiniteLocallyConstantSheaf.cokernel g
  apply isFiniteLocallyConstant_of_iso
    (PreservesCokernel.iso V g ≪≫ cokernel.mapIso _ f eM eN ?_)
  · exact isFiniteLocallyConstant_comparisonUpperStar_obj (cokernel g)
  · simp [g]

end AlgebraicGeometry.ProEtale
