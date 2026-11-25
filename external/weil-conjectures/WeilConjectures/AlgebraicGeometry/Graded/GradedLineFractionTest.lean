/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedLineFractionChart.GradedLineFractionChart
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Graded.GradedLineFractionTestLocal

/-! # Comparison of graded line fraction charts with a trivialized Proj map

Source: Stacks Project, Constructions, Tags 01NK and 01O9
(blueprint: lem-trf-graded-line-fraction-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism with all prescribed fraction restrictions has the usual formula on any
trivialized open test with unit irrelevant ideal. This is a comparison lemma for an
already supplied morphism, not an existence assertion or a statement that it is over S.

Source: Stacks Project, Constructions, Tag 01NK, lemma-invertible-map-into-proj,
and Tag 01O9, lemma-invertible-map-into-relative-proj, characterizations (2) and (3)
(blueprint: lem-trf-graded-line-fraction-test).

Proof: The unit-irrelevant-ideal hypothesis covers the test by basic opens of the
images under alpha of positive-degree homogeneous elements. Refine these opens by
affine opens on which the pulled-back trivialization comes from a local frame of L.
For an open immersion, the tensor-pullback section and power comparisons identify
psi.evaluate with restriction of psi.component. Thus the displayed equality for alpha
says that its degree-n value is the coefficient in the n-th power of this frame.
The uniqueness of coefficients in a free generator identifies these coefficients
with c. Each refined basic open therefore maps through the corresponding source
localization chart. Its given restriction to F and Mathlib's fromOfGlobalSections map
have the same image of every homogeneous fraction. The affine adjunction identifies
their maps into the standard Proj chart. Compose with the relative-Proj chart embedding
and glue these equalities on the test. This proves the formula without imposing an
extra generation hypothesis on T. Empty tests and exponent-zero fractions are included. -/
theorem gradedLineFraction_test
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ)
    (F : T ⟶ A.relProj)
    (hF : ∀ i : GradedLineFractionChart h A L, i.source c ≫ F = i.target c ρ)
    (W : Scheme.{u}) (j : W ⟶ T) (hj : IsOpenImmersion j)
    (V : S.affineOpens) (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (α : A.obj V →+* Γ(W, ⊤))
    (hα : ∀ (n : ℕ) (a : A.grading V n), α a =
      (unitSectionsEquiv ⊤).symm
        ((AlgebraicSpace.trivializedPower e n).hom.app ⊤ (ψ.evaluate j V q n a)))
    (hαgen : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤) :
    j ≫ F = Proj.fromOfGlobalSections (A.grading V) α hαgen ≫ A.relProjι V := by
  apply Scheme.hom_ext_of_forall
  exact gradedLineFraction_test_local ψ P hP0 hPs c hc ρ hρ F hF W j hj V q e α hα hαgen

end AlgebraicGeometry.Scheme.Modules
