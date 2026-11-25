/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix

import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient

/-! # Transport of regular-module scalars to a geometric point

Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

@[irreducible] private noncomputable def transportedCoordinates
    {C : Type*} [Category C] {E : Type u} [Field E]
    (H : C ⥤ ModuleCat.{u + 1} E) {A B : C} (t : A ≅ B)
    (b₀ : H.obj B ≃ₗ[E] E) : H.obj A ≃ₗ[E] E :=
  (H.mapIso t).toLinearEquiv.trans b₀

private lemma conjugatedScalar
    {C : Type*} [Category C] {E : Type u} [Field E]
    (H : C ⥤ ModuleCat.{u + 1} E) {A B : C} (t : A ≅ B)
    (b₀ : H.obj B ≃ₗ[E] E) (f : A ⟶ A) :
    transportedCoordinates H t b₀
        (H.map f ((transportedCoordinates H t b₀).symm 1)) =
      b₀ (H.map (t.inv ≫ f ≫ t.hom) (b₀.symm 1)) := by
  unfold transportedCoordinates
  change b₀ ((H.map t.hom) ((H.map f) ((H.map t.inv) (b₀.symm 1)))) = _
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- Coordinate transport reduces scalar computation to conjugation. -/
theorem condensedField_coordinates_of_conjugacy
    {C D : Type*} [Category C] [Category D] {E : Type u} [Field E]
    (P : C ⥤ D) (H : D ⥤ ModuleCat.{u + 1} E) (A : C) (B : D)
    (t : P.obj A ≅ B) (cB : (B ⟶ B) → E) {cA : (A ⟶ A) → E}
    (hB : ∃ b₀ : H.obj B ≃ₗ[E] E, ∀ f, b₀ (H.map f (b₀.symm 1)) = cB f)
    (hc : ∀ f, cB (t.inv ≫ P.map f ≫ t.hom) = cA f) :
    ∃ b : (P ⋙ H).obj A ≃ₗ[E] E,
      ∀ f, b ((P ⋙ H).map f (b.symm 1)) = cA f := by
  obtain ⟨b₀, hb₀⟩ := hB
  refine ⟨transportedCoordinates H t b₀, fun f ↦ ?_⟩
  exact (conjugatedScalar H t b₀ (P.map f)).trans
    ((hb₀ (t.inv ≫ P.map f ≫ t.hom)).trans (hc f))

/-- Transport the normalized regular-module evaluation along one geometric map.

Source: Hemo--Richarz--Scholbach, Example 3.1; the adjoint-test characterization of
continuous realization in `condensedFieldContinuousMapIso_test`
(auxiliary; not a blueprint node).

Proof in words. Restriction along the inverse coefficient isomorphism sends the
regular pulled-back coefficient module to the regular coefficient module on V.
The canonical isomorphism is the coefficient isomorphism itself. Module inverse image
along a sends that regular module to the regular coefficient module on Spec Ω, by the
strong monoidality of inverse image and the extension-of-scalars regular-module
comparison. Let t denote their composite. Apply H to t and compose with the given
regular-module coordinate b on Spec Ω; this gives the required linear equivalence.
Conjugation by t transports every regular-module endomorphism f. The normalization
of H computes its scalar from the canonical continuous realization on Spec Ω.
The adjoint-test equation for that realization, naturality of the unit, and the
coefficient pullback comparison identify this transported coefficient with the
pullback along a of the continuous coefficient of f on V. A continuous function
pulled back to Spec Ω has value at z equal to its original value at a(z). This proves
the formula. The argument needs no finite presentation and is valid for any H with
the stated normalization; a zero functor cannot satisfy that normalization. -/
theorem condensedField_geometric_evaluation_scalars
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X V : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (p : V ⟶ X) (a : Spec (.of Ω) ⟶ V) (z : Spec (.of Ω))
    (H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
      (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω))) ⥤
      ModuleCat.{u + 1} E)
    (hH : CondensedFieldPointScalarProperty E Ω z H) :
    let R := condensedRingObj (condensedFieldCoefficientRingObj E) X
    let Ri := (upperStar AddCommGrpCat.{u + 1} p).obj R
    let F :=
      condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) p a ⋙ H
    ∃ b : F.obj (Mod.regular Ri) ≃ₗ[E] E,
      ∀ f : Mod.regular Ri ⟶ Mod.regular Ri,
        b (F.map f (b.symm 1)) =
          condensedFieldContinuousCoefficientMap E V
            (inv (condensedFieldPullbackRealization E p) ≫ f.hom ≫
              condensedFieldPullbackRealization E p) (a z) := by
  dsimp (config := { proj := false }) only
  apply condensedField_coordinates_of_conjugacy
    (condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) p a)
    H (Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X)))
    (Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω))))
    (condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a)
    (condensedFieldPointCoefficient E Ω z) hH
  intro f
  exact condensedField_geometric_regular_coefficient E Ω p a z f

end AlgebraicGeometry.ProEtale
