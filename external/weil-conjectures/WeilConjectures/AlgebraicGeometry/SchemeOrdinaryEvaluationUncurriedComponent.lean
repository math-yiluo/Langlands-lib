/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Uncurried ordinary evaluation component
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Cancellation of the ordinary component equation under tensor-Hom uncurrying.
Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DQ;
ordinary evaluation chain calculation, step 3, cancellation portion.
(blueprint: lem-pc-scheme-ordinary-uncurried-component).

Proof: The equality n+r=k identifies k with r+n, so apply hf at p,q,n,r.
Apply tensorHomEquiv.symm to the component equation and precompose with the
braiding of F^p tensor V^q and P^r. If r+q=0, the inverse laws for tensorHomEquiv
cancel its forward application. Symmetry cancels the two successive braidings,
leaving precisely the associator, dual projection, single-unit identification,
right unitor and the degree transport displayed on the right. The degree sums
and r+q=0 imply p=k; proof irrelevance identifies the degree transports. If
r+q is nonzero, hf gives zero. Under the monoidal closed structure supplied by
tensorClosed, uncurrying is a tensor whiskering followed by evaluation, hence
sends zero to zero by monoidal preadditivity. Precomposition also preserves zero.
The argument is valid in every integer degree and for zero complexes. -/
theorem schemeOrdinaryEvaluation_uncurried_component (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f)
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    (β_ (F.X p ⊗ V.X q) (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (F.X p ⊗ V.X q)
        (F.X k)).symm
        (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ≫
          f.f n ≫ π P F n r k (by omega)) =
    (if h : r + q = 0 then
      (α_ (F.X p) (V.X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ (V.X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (V.X q)
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).symm
              (π P O q r 0 h ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = k)).hom
    else 0) := by
  classical
  have hk : k = r + n := by omega
  revert hnr
  subst k
  intro hnr
  dsimp only
  have he := congrArg (fun t ↦
    (β_ (F.X p ⊗
      (homComplex (R := Y.sheaf) P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))).X q) (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) _
        (F.X (r + n))).symm t) (hf p q n r hpq)
  apply he.trans
  by_cases h : r + q = 0
  · simp only [dite_eq_left h, Equiv.symm_apply_apply, SymmetricCategory.symmetry_assoc]
  · let := SheafOfModules.monoidalClosed (R := Y.sheaf)
    have : MonoidalPreadditive
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
      Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
    simp only [dite_eq_right h, ← SheafOfModules.uncurry_eq_tensorHomEquiv_symm (R := Y.sheaf),
      MonoidalClosed.uncurry_eq, MonoidalPreadditive.whiskerLeft_zero, comp_zero, zero_comp]

end AlgebraicGeometry
