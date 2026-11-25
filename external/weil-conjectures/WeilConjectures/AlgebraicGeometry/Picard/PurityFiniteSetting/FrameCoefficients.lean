/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer

/-! # Coefficient twists and support boundaries of an étale frame

Finite coefficient twists, their pullbacks, and the closed-open support boundary.
Part of the construction in
`WeilConjectures.AlgebraicGeometry.Picard.PurityFiniteSetting.FrameClass`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting


/-- The finite clause of the coefficient twists, in fixed-scalar coordinates.
This reuses the finite Tate sheaves and exact comparison inverse image. -/
def frameCoefficientTwist (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u}) (d : ℕ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
    (Scheme.finiteEtaleTateTwist X P.exponent P.Coefficient
      (P.exponent_coefficient_eq_zero h) d)

/-- Multiplication of nonnegative finite twists, obtained from the tensor
powers through the strong monoidal comparison. Degree zero uses its unit constraint. -/
def frameCoefficientTensorNext (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u}) :
    (d : ℕ) → P.frameCoefficientTwist h X d ⊗ P.frameCoefficientTwist h X 1 ≅
      P.frameCoefficientTwist h X (d + 1)
  | 0 => by
    let ν := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
    let e : P.frameCoefficientTwist h X 0 ≅ 𝟙_ _ :=
      ν.mapIso (Functor.Monoidal.εIso
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).symm ≪≫
        (Functor.Monoidal.εIso ν).symm
    exact tensorIso e (Iso.refl _) ≪≫ λ_ _
  | d + 1 => by
    exact Functor.Monoidal.μIso
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (Scheme.finiteEtaleTateTwist X P.exponent P.Coefficient
        (P.exponent_coefficient_eq_zero h) (d + 1))
      (Scheme.finiteEtaleTateLine X P.exponent P.Coefficient
        (P.exponent_coefficient_eq_zero h))

/-- The finite degree-one cartesian twist comparison. The map is the exact inverse image
of the canonical scalar-extension map on roots, including the site-comparison square.
Its inverse is the inverse of this specified isomorphism, with no existence choice. -/
def frameCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Spec (.of P.field.k)) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
      (P.frameCoefficientTwist h Y 1) ≅ P.frameCoefficientTwist h X 1 := by
  letI := P.isIso_twistEtalePullback h f (P.exponent_isUnit Y a)
  exact (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) f).app
      (P.twistEtale h Y) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso
      (asIso (P.twistEtalePullback h f))

/-- The finite coefficient support connecting morphism in degree one. Its construction
is the Yoneda splice with the canonical localization sequence; it has degree two. -/
def frameSupportBoundary (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (f : Γ(X, ⊤))
    (L : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (κ : Abelian.Ext
      ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
          (P.constant X))) L 1) :
    Abelian.Ext ((lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (X.zeroLocusSubschemeι {f})).obj (P.constant (X.zeroLocusSubscheme {f}))) L 2 := by
  let i := X.zeroLocusSubschemeι {f}
  let j := (X.basicOpen f).ι
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    dsimp only [i, j]
    rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  exact (Abelian.Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
    (P.frameConstantPullback i).inv)).comp
      ((shortExact_openClosedShortComplex i j hij (P.constant X)).extClass.comp
        κ (rfl : 1 + 1 = 2)) (zero_add 2)

end WeilConjectures.PurityFiniteSetting
