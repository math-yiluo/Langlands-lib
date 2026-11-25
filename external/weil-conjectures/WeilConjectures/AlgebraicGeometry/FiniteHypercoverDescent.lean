/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts

/-!
# Blueprint statements

lemma-weil-pbc-finite-hypercover-descent.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Blueprint: corollary-cohomology-pro-etale-affine. -/
theorem finite_hypercover_descent
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    (∀ (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover c.pt r),
      ∃ (i : Iᵒᵖ) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj i) r),
        Ui.IsBaseChange (c.π.app i) U ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i) (n : Fin (r + 1)),
            Surjective ((Over.pullback (D.map h)).map
              ((Scheme.Etale.forget (D.obj i)).map (Ui.matchingMap n))).left) ∧
    (∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ : U.diagram ⋙ Over.pullback (c.π.app i) ⟶
        V.diagram ⋙ Over.pullback (c.π.app i)),
      ∃ (j : Iᵒᵖ) (h : j ⟶ i)
        (ψ : U.diagram ⋙ Over.pullback (D.map h) ⟶
          V.diagram ⋙ Over.pullback (D.map h)),
        ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
          (Over.pullback (c.π.app j)).map (ψ.app Δ) ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                  (c.w h))).app (V.diagram.obj Δ)).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
              eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                (c.w h))).app (U.diagram.obj Δ)).hom ≫ φ.app Δ) ∧
    (∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ ψ : U.diagram ⟶ V.diagram),
      Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
        Functor.whiskerRight ψ (Over.pullback (c.π.app i)) →
      ∃ (j : Iᵒᵖ) (h : j ⟶ i),
        Functor.whiskerRight φ (Over.pullback (D.map h)) =
          Functor.whiskerRight ψ (Over.pullback (D.map h))) := by
  exact ⟨finite_hypercover_descent_objects D c hc,
    finite_hypercover_descent_morphisms D c hc,
    finite_hypercover_descent_equalities D c hc⟩

end AlgebraicGeometry
