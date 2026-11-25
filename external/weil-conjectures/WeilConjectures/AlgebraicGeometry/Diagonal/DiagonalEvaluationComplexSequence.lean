/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalReductionCompletion

/-! # Integral multiplication sequences for evaluated reduction
Source: diagonal tower system proof, step (2).
(blueprint: lem-sfb-diagonal-evaluation-complex-sequence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

section
variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  {ℓ : ℕ} {L : A ⥤ B} (U : B ⥤ A) [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L) (n : ℕ)

/-- Apply the quotient-unit map termwise, retaining the canonical identity and
composition comparisons of complexes.
Source: diagonal tower system proof, step (2)
(blueprint: lem-sfb-diagonal-evaluation-complex-sequence). -/
def diagonalEvaluationComplexMap (P : CochainComplex A ℤ) :
    P ⟶ ((diagonalEvaluationForget U n).mapHomologicalComplex (.up ℤ)).obj
      ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n) (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (D.ordinary.E ⋙
      diagonalEvaluationForget U n)) (.up ℤ)).inv.app P

omit [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
/-- Components of the actual quotient-unit complex map.
Source: termwise definition
(blueprint: lem-sfb-diagonal-evaluation-complex-sequence). -/
theorem diagonalEvaluationComplexMap_f (P : CochainComplex A ℤ) (i : ℤ) :
    (diagonalEvaluationComplexMap U ad D n P).f i =
      (diagonalEvaluationQuotient U ad D n).app (P.X i) := by
  simp only [diagonalEvaluationComplexMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f]
  change (𝟙 (P.X i)) ≫ (diagonalEvaluationQuotient U ad D n).app (P.X i) ≫
    (𝟙 ((diagonalEvaluationForget U n).obj (D.ordinary.E.obj (P.X i)))) = _
  rw [Category.id_comp]
  exact Category.comp_id _

end

attribute [local irreducible] diagonalScalarExtension diagonalForget diagonalScalarAdjunction
  reductionPresentation

/-- On a torsion-free representative the underlying evaluated quotient gives a
short exact multiplication sequence.
Source: diagonal tower system proof, step (2).
(blueprint: lem-sfb-diagonal-evaluation-complex-sequence).
Proof: compare the p-adic quotient to the integral quotient using the existing
ordinary_level_comparison, which carries the scalar-adjunction unit to the quotient
map. The integral cokernel presentation is short exact because the supplied
multiplication map is degreewise monic. Transport it by this quotient comparison
in every degree, then use the degreewise short-exactness criterion for complexes. -/
theorem diagonal_evaluation_complex_shortExact
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (P : CochainComplex (DiagonalAb W) ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) (n : ℕ) :
    ∃ hz : (ℓ ^ (n + 1) • 𝟙 P) ≫
        diagonalEvaluationComplexMap (diagonalForget ℓ W) (diagonalScalarAdjunction ℓ W)
          D n P = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  let I := reductionPresentation ℓ (𝟭 (DiagonalAb W))
  let q := diagonalEvaluationComplexMap (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D n P
  have hq (i : ℤ) : q.f i = (diagonalScalarAdjunction ℓ W).unit.app (P.X i) ≫
      (diagonalForget ℓ W).map ((D.ordinary.π n).app (P.X i)) := by
    rw [diagonalEvaluationComplexMap_f]
    rfl
  have hz : (ℓ ^ (n + 1) • 𝟙 P) ≫ q = 0 := by
    ext i : 1
    obtain ⟨e, he⟩ := ordinary_level_comparison ℓ W D.ordinary I n (P.X i)
    change (ℓ ^ (n + 1) • 𝟙 (P.X i)) ≫ q.f i = 0
    apply (cancel_mono e.hom).1
    change ((ℓ ^ (n + 1) • 𝟙 (P.X i)) ≫
      ((diagonalScalarAdjunction ℓ W).unit.app (P.X i) ≫
        (diagonalForget ℓ W).map ((D.ordinary.π n).app (P.X i)))) ≫ e.hom = 0 ≫ e.hom
    rw [Category.assoc]
    change (ℓ ^ (n + 1) • 𝟙 (P.X i)) ≫
      ((diagonalScalarAdjunction ℓ W).unit.app (P.X i) ≫
        (diagonalForget ℓ W).map ((D.ordinary.π n).app (P.X i)) ≫ e.hom) = 0 ≫ e.hom
    rw [he, zero_comp]
    exact I.zero n (P.X i)
  refine ⟨hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hP n i
  have : Epi ((I.π n).app (P.X i)) := by
    exact Cofork.IsColimit.epi (I.quotient n (P.X i))
  have hs : (ShortComplex.mk (ℓ ^ (n + 1) • 𝟙 (P.X i))
      ((I.π n).app (P.X i)) (I.zero n (P.X i))).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (I.quotient n (P.X i)) }
  obtain ⟨e, he⟩ := ordinary_level_comparison ℓ W D.ordinary I n (P.X i)
  apply (ShortComplex.shortExact_iff_of_iso
    (ShortComplex.isoMk (S₁ := (ShortComplex.mk _ q hz).map
      (HomologicalComplex.eval (DiagonalAb W) (.up ℤ) i))
      (S₂ := ShortComplex.mk _ _ (I.zero n (P.X i)))
      (Iso.refl _) (Iso.refl _) e ?_ ?_)).2 hs
  · change (𝟙 (P.X i)) ≫ (ℓ ^ (n + 1) • 𝟙 (P.X i)) =
      (ℓ ^ (n + 1) • 𝟙 P).f i ≫ (𝟙 (P.X i))
    simp only [HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f,
      Category.comp_id, Category.id_comp]
  · change (𝟙 (P.X i)) ≫ (I.π n).app (P.X i) = q.f i ≫ e.hom
    have he' :
        ((diagonalScalarAdjunction ℓ W).unit.app (P.X i) ≫
          (diagonalForget ℓ W).map ((D.ordinary.π n).app (P.X i))) ≫ e.hom =
          (I.π n).app (P.X i) := by
      simpa only [Category.assoc] using he
    exact (Category.id_comp _).trans (he'.symm.trans
      (congrArg (fun f ↦ f ≫ e.hom) (hq i).symm))

end AlgebraicGeometry.ProEtale
