/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData

import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback

/-! # Continuous functions for integral matrix charts

The analytic part of the pivot argument supplies a dominating, nowhere zero entry.
The module-object block decomposition is constructed separately.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem cover_of_open_neighborhoods {X : Scheme.{u}}
    (V : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (P : ∀ (Y : Scheme.{u}), (Y ⟶ X) → Prop)
    (h : ∀ k (x : V.X k), ∃ U : (V.X k).Opens,
      x ∈ U ∧ P U.toScheme (U.ι ≫ V.f k)) :
    ∃ W : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ k, P (W.X k) (W.f k) := by
  classical
  choose U hxU hU using h
  let C (k : V.I₀) : (V.X k).OpenCover :=
    (V.X k).openCoverOfIsOpenCover (U k) (by
      apply eq_top_iff.mpr
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU k x⟩)
  let D (k : V.I₀) : Scheme.Cover.{u} Scheme.proetalePrecoverage (V.X k) :=
    ((C k).changeProp (Q := @Etale) (fun _ ↦ inferInstance)).weaken
      Scheme.etalePrecoverage_le_proetalePrecoverage
  exact ⟨V.bind D, fun k ↦ hU k.1 k.2⟩

set_option linter.unusedVariables false in
/-- After a rational cokernel trivialization, a map between standard finite free modules
admits analytic pivot charts.

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10 and Proposition 6.8.11(1);
the continuous-function pivot argument is an agent reduction.
(auxiliary; not a blueprint node)

Proof: refine the supplied cover, transport the standard finite-free bases along the
coefficient pullback comparisons, and use the canonical comparison with continuous
O_E-functions. Its monoid property, isomorphism and compatibility with O_E to E are
proved in ContinuousCoefficientRealizations.
Exact geometric-field evaluation computes the rational cokernel dimension as target
rank minus matrix rank. The rank is therefore constant on each cover member. If the
matrix is zero at any point, it is zero everywhere, and faithfulness of the continuous
matrix realization gives the zero alternative. Otherwise every point has a nonzero
entry. Choose one of maximal norm there. Intersect the finitely many open loci where
the change in each entry has norm strictly below this positive maximum. The ultrametric
inequality makes the chosen entry nowhere zero with constant norm on this neighborhood
and bounds every other entry by it. Transport the bases and realization to these opens
and compose covers. Empty members and zero source or target ranks use the zero branch.
The conclusion only concerns continuous coefficients, not divisibility or module blocks. -/
theorem integralMatrix_analytic_cover (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t₀ : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t₀)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      let f := (integralFiniteFreePullbackIso ℓ E (V.f k) n).inv ≫ T.map a ≫
        (integralFiniteFreePullbackIso ℓ E (V.f k) t₀).hom
      T.map a = 0 ∨ ∃ (i : Fin t₀) (j : Fin n),
        (∀ x, (integralMatrixFunctions ℓ E (V.X k)
          (chartComparison (V.X k) (continuousIntegers ℓ E)) f i j x).val ≠ 0) ∧
        ∀ r s x,
          ‖(integralMatrixFunctions ℓ E (V.X k)
            (chartComparison (V.X k) (continuousIntegers ℓ E)) f r s x).val‖ ≤
          ‖(integralMatrixFunctions ℓ E (V.X k)
            (chartComparison (V.X k) (continuousIntegers ℓ E)) f i j x).val‖ := by
  classical
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  obtain ⟨V, hV⟩ := integralMatrix_zero_neighborhood ℓ E n t₀ X a hC
  have hlocal (k : V.I₀) (x : V.X k) :
      ∃ U : (V.X k).Opens, x ∈ U ∧
        ((integralMatrixPullback ℓ E (U.ι ≫ V.f k)).map a = 0 ∨
          ∃ (i : Fin t₀) (j : Fin n),
            (∀ y : U.toScheme,
              (integralMatrixPullbackFunctions ℓ E (U.ι ≫ V.f k) a i j y).val ≠ 0) ∧
            ∀ r s (y : U.toScheme),
              ‖(integralMatrixPullbackFunctions ℓ E (U.ι ≫ V.f k) a r s y).val‖ ≤
              ‖(integralMatrixPullbackFunctions ℓ E (U.ι ≫ V.f k) a i j y).val‖) := by
    by_cases hz : ∀ i j, integralMatrixPullbackFunctions ℓ E (V.f k) a i j x = 0
    · obtain ⟨U, hxU, hU⟩ := hV k x hz
      exact ⟨U, hxU, Or.inl hU⟩
    · push Not at hz
      obtain ⟨i, j, hij⟩ := hz
      let b : Fin t₀ × Fin n → C(V.X k, E) := fun p ↦
        ⟨fun y ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a p.1 p.2 y).val,
          continuous_subtype_val.comp
            (integralMatrixPullbackFunctions ℓ E (V.f k) a p.1 p.2).continuous⟩
      have hb : ∃ p, b p x ≠ 0 :=
        ⟨(i, j), fun h ↦ hij (Subtype.ext h)⟩
      obtain ⟨W, p, hW, hxW, hp, hbound⟩ :=
        ContinuousMap.exists_open_dominating_member b x hb
      let U : (V.X k).Opens := ⟨W, hW⟩
      refine ⟨U, hxW, Or.inr ⟨p.1, p.2, ?_, ?_⟩⟩
      · intro y
        rw [integralMatrixFunctions_pullback]
        exact hp y.val y.property
      · intro r s y
        rw [integralMatrixFunctions_pullback, integralMatrixFunctions_pullback]
        exact hbound (r, s) y.val y.property
  have hcover := cover_of_open_neighborhoods V
    (fun Y g ↦ (integralMatrixPullback ℓ E g).map a = 0 ∨
      ∃ (i : Fin t₀) (j : Fin n),
        (∀ y, (integralMatrixPullbackFunctions ℓ E g a i j y).val ≠ 0) ∧
        ∀ r s y, ‖(integralMatrixPullbackFunctions ℓ E g a r s y).val‖ ≤
          ‖(integralMatrixPullbackFunctions ℓ E g a i j y).val‖) hlocal
  simpa only [integralMatrixPullbackFunctions, integralMatrixPullbackMap,
    integralMatrixPullback] using hcover

end AlgebraicGeometry.ProEtale.CondensedRing
