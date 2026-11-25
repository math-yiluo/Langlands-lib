/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
/-!
# Coherent comparison of etale and pro-etale inverse images

Source: blueprint, chap-Proper-base-change, theorem-proper-base-change-classical-pro,
node proposition-comparison-etale-derived-category--5; Stacks Project, Tags 098T, 099R, 00WX and
0B65 (blueprint: proposition-comparison-etale-derived-category--5).

The auxiliary interfaces extend the existing Kan-extension constructions to sets as
well as abelian groups and finite fixed-ring modules. Every comparison is the mate
of the canonical base-change isomorphism on restriction functors. No arbitrary
isomorphism is selected.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology D]
variable [∀ X : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology X) D]

/-- The constructed etale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable abbrev cbcEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable abbrev cbcEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cbcEtaleComparisonPullback D f ⊣ Etale.lowerStar D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The constructed proEtale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable abbrev cbcProEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable abbrev cbcProEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The comparison inverse image, constructed by left Kan extension and sheafification.
It is definitionally `comparisonUpperStar` for abelian coefficients and the left adjoint
of `Scheme.proEtaleSiteComparison` for sets.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable abbrev cbcComparisonCoefficientPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical comparison adjunction for the common coefficient category.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable abbrev cbcComparisonCoefficientAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The comparison inclusion commutes with the actual chosen base change.
Source: Stacks, Tag 099R; blueprint, proof step 1
(blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable def cbcComparisonSiteBaseChangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.toProEt Y ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ≅
      MorphismProperty.Over.pullback @Etale ⊤ f ⋙ Scheme.toProEt X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; simp; rfl)

/-- The canonical right-image comparison, induced by the chosen fibre products.
Its components identify sections over the same base change, including for sets.
Source: Stacks, Tags 099R and 00WX; blueprint, proof step 1
(blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable def cbcComparisonCoefficientDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    lowerStar D f ⋙ comparisonLowerStar D Y ≅
      comparisonLowerStar D X ⋙ Etale.lowerStar D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  have := Scheme.ProEt.isContinuous_overPullback f
  have := Scheme.isContinuous_toProEt X
  have := Scheme.isContinuous_toProEt Y
  have := Functor.isContinuous_comp (Scheme.toProEt Y)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    Y.smallEtaleTopology (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have := Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f)
    (Scheme.toProEt X) Y.smallEtaleTopology X.smallEtaleTopology (Scheme.ProEt.topology X)
  Functor.sheafPushforwardContinuousComp (Scheme.toProEt Y)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D Y.smallEtaleTopology
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) ≪≫
    Functor.sheafPushforwardContinuousIso (cbcComparisonSiteBaseChangeIso f) D
      Y.smallEtaleTopology (Scheme.ProEt.topology X) ≪≫
    (Functor.sheafPushforwardContinuousComp (MorphismProperty.Over.pullback @Etale ⊤ f)
      (Scheme.toProEt X) D Y.smallEtaleTopology X.smallEtaleTopology
        (Scheme.ProEt.topology X)).symm

/-- The canonical inverse-image comparison, normalized as the conjugate of
`cbcComparisonCoefficientDirectImageIso`, which evaluates on `W` as the identity on
sections over `W ×[Y] X`. This extends the inverse of
`comparisonUpperStarCompUpperStarIso` to set coefficients.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: proposition-comparison-etale-derived-category--5). -/
noncomputable def cbcComparisonCoefficientPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cbcEtaleComparisonPullback D f ⋙ cbcComparisonCoefficientPullback D X ≅
      cbcComparisonCoefficientPullback D Y ⋙ cbcProEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv
    ((cbcEtaleComparisonAdjunction D f).comp (cbcComparisonCoefficientAdjunction D X))
    ((cbcComparisonCoefficientAdjunction D Y).comp (cbcProEtaleComparisonAdjunction D f))).symm
      (cbcComparisonCoefficientDirectImageIso D f).symm).symm

end ProEtale
end AlgebraicGeometry
