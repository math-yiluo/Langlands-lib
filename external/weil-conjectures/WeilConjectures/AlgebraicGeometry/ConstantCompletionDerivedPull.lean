/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryPullComparison
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Constant coefficient completion: DerivedPull

The derived scalar pullback comparison.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
attribute [local semireducible] completed
attribute [local irreducible] completed
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] derivedPull pull change

/-- The prescribed unreduced ordinary scalar comparison. Source: Stacks 06YY, 099L
(auxiliary; not a blueprint node). -/
def ordinaryPullComparison (A : Type u) [CommRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
      pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) :=
  (ordinaryPullComparison_existsUnique F A I).exists.choose

/-- The representative square for a derived scalar comparison, with abstract ordinary
functors so complex-composition conversions are checked before specialization.
Source: Stacks 06YY, 099L
(auxiliary; not a blueprint node). -/
def DerivedPullComparisonFormula
    {M₀ M₁ M₂ M₃ D₀ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (α : r.mapHomologicalComplex (.up ℤ) ⋙ q₁ ≅ q₀ ⋙ dr)
    (βp : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ⟶ b ⋙ s)
    (βb : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (δ : s.mapHomologicalComplex (.up ℤ) ⋙ q₃ ≅ q₂ ⋙ ds)
    (e : dr ⋙ dp ⟶ db ⋙ ds) (P : CochainComplex M₀ ℤ) : Prop :=
  dp.map (α.inv.app P) ≫ βp.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₃.map ((NatTrans.mapHomologicalComplex γ (.up ℤ)).app P) =
    e.app (q₀.obj P) ≫ ds.map (βb.app P) ≫
      δ.inv.app ((b.mapHomologicalComplex (.up ℤ)).obj P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_module_square
    {M₀ M₁ M₂ M₃ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Abelian M₀] [HasDerivedCategory M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : DerivedCategory M₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃}
    {db : DerivedCategory M₀ ⥤ D₂}
    (α : r.mapHomologicalComplex (.up ℤ) ⋙ q₁ ≅ DerivedCategory.Q ⋙ dr)
    (βp : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ⟶ b ⋙ s)
    (βb : DerivedCategory.Q ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (δ : s.mapHomologicalComplex (.up ℤ) ⋙ q₃ ≅ q₂ ⋙ ds)
    (P : CochainComplex M₀ ℤ → Prop)
    (hres : ∀ X : CochainComplex M₀ ℤ,
      ∃ (K : CochainComplex M₀ ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hβb : ∀ X, P X → IsIso (βb.app X)) :
    ∃! e : dr ⋙ dp ⟶ db ⋙ ds, ∀ X, P X →
      DerivedPullComparisonFormula DerivedCategory.Q q₁ q₂ q₃ r s p b
        α βp γ βb δ e X := by
  exact resolving_square q₁ q₂ q₃
    (r.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
    (p.mapHomologicalComplex (.up ℤ)) (s.mapHomologicalComplex (.up ℤ))
    dr db dp ds α βp (NatTrans.mapHomologicalComplex γ (.up ℤ)) βb δ P hres hβb

section
attribute [local irreducible] dres

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical derived scalar comparison, characterized on every flat-term K-flat
representative. Uniqueness makes it independent of resolving choices and gives its
coherence for identity and composite inverse images with the same insertion formula.
Source: Stacks 06YY, 099L (auxiliary; not a blueprint node).
Proof: restrict a flat-term K-flat B-model, using flatness of B over the constant ring.
Apply ordinaryPullComparison termwise, then the two universal computation maps. This
is invariant under resolution maps by the resolving-class derived-functor theorem, and
hence descends naturally to every derived object. The square determines it on a resolving
class, hence uniquely. For composite inverse images, both formulas send m to
(1 tensor (1 tensor m)), identified with 1 tensor m by ordinary tensor reassociation;
therefore uniqueness gives composition and identity coherence. -/
theorem derivedPullComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! δ : dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
        (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I),
      ∀ P : Cx (completed J A I), P.IsKFlatTensor →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedPullComparisonFormula (Q (completed J A I)) (Q (constant J A))
          (Q (completed J' A I)) (Q (constant J' A))
          (res (coefficientMap J A I)) (res (coefficientMap J' A I))
          (pull F (constantMap F A)) (pull F (completedMap F A I))
          (resFactors (coefficientMap J A I))
          (derivedPull F V adj (constantMap F A)).comparison
          (ordinaryPullComparison F A I)
          (derivedPull F V adj (completedMap F A I)).comparison
          (resFactors (coefficientMap J' A I)) δ P
        := by
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J' A I))
  let := HasDerivedCategory.standard (Mod (constant J' A))
  let φ := coefficientMap J A I
  let ψ := coefficientMap J' A I
  let p := derivedPull F V adj (constantMap F A)
  let b := derivedPull F V adj (completedMap F A I)
  let P (X : Cx (completed J A I)) :=
    X.IsKFlatTensor ∧ ∀ q : ℤ, SheafOfModules.IsFlat (X.X q)
  obtain ⟨e, he, hu⟩ := resolving_module_square
    (Q (constant J A)) (Q (completed J' A I)) (Q (constant J' A))
    (res φ) (res ψ) (pull F (constantMap F A)) (pull F (completedMap F A I))
    (resFactors φ) p.comparison
    (ordinaryPullComparison F A I)
    b.comparison (resFactors ψ) P (module_flat_kFlat_resolution (J := J))
    (fun X hX ↦ b.computation X hX.1 hX.2)
  refine ⟨e, ?_, ?_⟩
  · intro X hk hf
    exact he X ⟨hk, hf⟩
  · intro t ht
    apply hu t
    intro X hX
    exact ht X hX.1 hX.2

end

/-- The actual derived comparison with the specified K-flat scalar-insertion formula.
Source: Stacks 06YY, 099L (auxiliary; not a blueprint node). -/
def derivedPullComparison (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
      (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I) :=
  (derivedPullComparison_existsUnique F V adj A I).exists.choose

end CategoryTheory.ConstantCompletion
