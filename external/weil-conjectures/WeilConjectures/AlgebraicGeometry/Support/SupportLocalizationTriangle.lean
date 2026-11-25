/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Support.SupportTriangleCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Support.SupportTriangleConstruction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective

/-!
# Localization for the ambient bounded-below exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`lemma-local-cohomology-right-adjoint--2` (blueprint: lemma-local-cohomology-right-adjoint--2).
The categories are all constant-coefficient module sheaves, as in
`definition-local-cohomology`; there is no constructibility condition. The right derived
functors below are the existing ordinary injective-derived functors on `D⁺`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorPlusCompatibility
  Functor.mapDerivedCategory
  Adjunction.derivedPlus

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  DerivedCategory.quotientCompQhIso

section GenericModelComparisons
universe v
variable {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- Transport a model isomorphism through an exact functor, with the fixed derived
factorization. Source: blueprint lemma-local-cohomology-right-adjoint--2, step 5
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def CategoryTheory.Functor.supportExactModelComparison
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex C ℤ) (K : DerivedCategory.Plus C)
    (e : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      (F.mapDerivedCategoryPlus.obj K).obj :=
  (F.mapDerivedCategoryFactors.app I).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    (F.mapDerivedCategoryPlusCompatibility.app K).symm

/-- Compute a right derived functor on a K-injective model with its fixed unit.
Source: blueprint lemma-local-cohomology-right-adjoint--2, steps 1 and 4
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def CategoryTheory.Functor.supportRightModelComparison
    [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      (F.rightDerivedFunctorPlus.obj K).obj :=
  (F.rightDerivedFunctorObjQIso I).symm ≪≫ F.rightDerivedFunctor.mapIso e ≪≫
    (F.rightDerivedFunctorPlusCompatibility.app K).symm

end GenericModelComparisons

section ExplicitTriangle
variable {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]

end ExplicitTriangle

section ModelComparison
universe v
variable {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [CategoryTheory.Abelian.HasKInjectiveResolutions C]

section Counit
variable [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

end Counit

section Unit
variable [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

end Unit

section NormalizedComparisons
variable [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

end NormalizedComparisons

end ModelComparison

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [hs : IsClosedImmersion s] [hj : IsOpenImmersion j] [hqc : QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

/-- The termwise-induced closed direct image on D⁺, using its exactness, rather than
an independently chosen functor. Source: blueprint lemma-local-cohomology-right-adjoint--2
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def supportClosedDerivedPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  (lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus

set_option linter.unusedSectionVars false in
/-- A model in the stated class is K-injective.
Source: Stacks Tag 070J; blueprint lemma-local-cohomology-right-adjoint--2, step 1
(blueprint: lemma-local-cohomology-right-adjoint--2).
Proof: choose a lower bound from hI. Its terms are injective by hI. Apply
CochainComplex.isKInjective_of_injective with that bound. -/
theorem supportModelKInjective (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) : I.IsKInjective := by
  obtain ⟨⟨n, hn⟩, hInj⟩ := hI
  have := hn
  have := hInj
  exact CochainComplex.isKInjective_of_injective I n

include hj in
set_option linter.unusedSectionVars false in
/-- Open restriction of a bounded below injective model is K-injective.
Source: Stacks Tag 08FI; blueprint lemma-local-cohomology-right-adjoint--2, step 4
(blueprint: lemma-local-cohomology-right-adjoint--2).
Proof: identify open inverse image with the slice restriction by
lem-weil-proetale-weakly-etale-localization. Its exact left adjoint, extension by
zero, implies that it preserves injectives (lemma-acyclicity-pulled-back-injectives).
It preserves the lower bound since it is additive. Apply Stacks Tag 070J. -/
theorem supportOpenModelKInjective (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) :
    CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨⟨n, hn⟩, hInj⟩ := hI
  have := hn
  have := hInj
  have hTerms : ∀ m : ℤ, Injective
      ((((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).X m) := fun m ↦
    injective_upperStar_obj_of_weaklyEtale (ModuleCat.{u + 1} Λ) j (I.X m)
  exact CochainComplex.isKInjective_of_injective _ n

/-- The canonical computation of Rs^! on the chosen model, normalized by the derived
functor unit and by the bounded/unbounded comparison; no model isomorphism is chosen.
Source: blueprint lemma-local-cohomology-right-adjoint--2, steps 1 and 3
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def supportShriekModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj
        (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K).obj :=
  letI := supportModelKInjective Λ I hI
  (finiteClosedUpperShriek Λ s j).supportRightModelComparison I K eB

/-- The canonical first-term comparison, using termwise exact s_* and the preceding
unit-normalized computation of Rs^!.
Source: blueprint lemma-local-cohomology-right-adjoint--2, step 5
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def supportFirstModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportedSectionsComplex Λ s j hPair I) ≅
      ((supportClosedDerivedPlus Λ s j hPair).obj
        ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).obj :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  (lowerStar (ModuleCat.{u + 1} Λ) s).supportExactModelComparison
    (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (.up ℤ)).obj I)
    ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)
    (supportShriekModelComparison Λ s j I hI K eB)

/-- The canonical third-term comparison, using injectivity after open restriction,
the derived functor unit, and the ordinary bounded/unbounded comparison for Rj_*.
Source: blueprint lemma-local-cohomology-right-adjoint--2, steps 4 and 5
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def supportThirdModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportCComplex Λ j I) ≅
      ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).obj :=
  letI := supportOpenModelKInjective Λ j I hI
  (lowerStar (ModuleCat.{u + 1} Λ) j).supportRightModelComparison
    (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex (.up ℤ)).obj I)
    ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)
    ((upperStar (ModuleCat.{u + 1} Λ) j).supportExactModelComparison I K eB)

attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek

private noncomputable def supportKernelIsKernel
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  isLimitOfHasKernelOfPreservesLimit
    ((evaluation _ _).obj M)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit

set_option linter.unusedSectionVars false in
private theorem supportMap_unit_zero
    (hPair : IsCompl (Set.range s) (Set.range j))
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (f : (lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶ M) :
    f ≫ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app M = 0 := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv _ _).symm.injective
  have hz := isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} Λ) s j
    hPair.disjoint N
  exact hz.eq_of_src _ _

attribute [local irreducible] supportKernelIsKernel

private noncomputable def supportSheafHomEquiv
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    ((lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶ M) ≃
      (N ⟶ (finiteClosedUpperShriek Λ s j).obj M) := by
  have := finiteSupportedClosedComparison_isIso Λ s j hPair
  let q := (asIso (finiteSupportedClosedComparison Λ s j)).app M
  let e : ((lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶ M) ≃
      ((lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶
        (finiteSupportedSections Λ j).obj M) :=
    { toFun := fun f ↦ (supportKernelIsKernel Λ j M).lift
        (KernelFork.ofι f (supportMap_unit_zero Λ s j hPair N M f))
      invFun := fun f ↦ f ≫ (finiteSupportedSectionsι Λ j).app M
      left_inv := by
        intro f
        exact (supportKernelIsKernel Λ j M).fac _ WalkingParallelPair.zero
      right_inv := by
        intro f
        apply Fork.IsLimit.hom_ext (supportKernelIsKernel Λ j M)
        exact (supportKernelIsKernel Λ j M).fac _ WalkingParallelPair.zero }
  exact e.trans ((Iso.homCongr (Iso.refl _) q).trans
    (fullyFaithfulLowerStar Λ s).homEquiv.symm)
private theorem supportSheafHomEquiv_symm
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (f : N ⟶ (finiteClosedUpperShriek Λ s j).obj M) :
    (supportSheafHomEquiv Λ s j hPair N M).symm f =
      (lowerStar (ModuleCat.{u + 1} Λ) s).map f ≫
        (supportModelInclusion Λ s j hPair).app M := by
  simp [supportSheafHomEquiv, supportKernelIsKernel, Iso.homCongr, supportModelInclusion]

attribute [local irreducible] supportSheafHomEquiv

private noncomputable def supportSheafAdjunction :
    lowerStar (ModuleCat.{u + 1} Λ) s ⊣ finiteClosedUpperShriek Λ s j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := supportSheafHomEquiv Λ s j hPair
      homEquiv_naturality_left_symm := by
        intros
        simp only [supportSheafHomEquiv_symm, Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro N M M' f g
        apply (supportSheafHomEquiv Λ s j hPair N M').symm.injective
        rw [Equiv.symm_apply_apply, supportSheafHomEquiv_symm, Functor.map_comp,
          Category.assoc]
        change f ≫ g = _ ≫
          (finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s).map g ≫ _
        rw [(supportModelInclusion Λ s j hPair).naturality g,
          ← Category.assoc, ← supportSheafHomEquiv_symm, Equiv.symm_apply_apply]
        rfl }

attribute [local irreducible] supportSheafAdjunction

private noncomputable def supportDerivedAdjunction :
    supportClosedDerivedPlus Λ s j hPair ⊣
      (finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus := by
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  exact (supportSheafAdjunction Λ s j hPair).derivedPlus

attribute [local irreducible] supportDerivedAdjunction
  supportShriekModelComparison supportFirstModelComparison supportThirdModelComparison

universe v w

end AlgebraicGeometry.ProEtale

section EtaleComparison
universe v
section GenericTriangle
variable {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

end GenericTriangle

open AlgebraicGeometry AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X U X' U' : Scheme.{u}} (j : U ⟶ X)
  (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
  [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v)

namespace AlgebraicGeometry.ProEtale

section
universe u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category C] [Category D]
  {L₁ L₂ L₃ L₄ : C ⥤ D} {R₁ R₂ R₃ R₄ : D ⥤ C}
  (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (d : L₄ ⊣ R₄)

end

section Mate
universe u₁ u₂ u₃ u₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category A] [Category B] [Category C] [Category D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

end Mate

attribute [local irreducible] upperStarComp upperStarCongr lowerStarComp lowerStarCongr
  upperStar lowerStar upperStarLowerStarAdjunction
  squareLowerStarIso baseChangeMap
  mateEquiv conjugateEquiv Adjunction.comp Functor.whiskerLeft Functor.whiskerRight

omit [Finite Λ] [Etale v] [Etale vU] in
omit [Finite Λ] [Etale v] [Etale vU] in
attribute [local irreducible] finiteSupportedSections finiteClosedUpperShriek
  supportModelInclusion

variable {Z Z' : Scheme.{u}} (s : Z ⟶ X) (vZ : Z' ⟶ Z) (s' : Z' ⟶ X')
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  [IsClosedImmersion s'] [IsOpenImmersion j'] [QuasiCompact j']
  (hPair : IsCompl (Set.range s) (Set.range j))
  (hPair' : IsCompl (Set.range s') (Set.range j'))

end AlgebraicGeometry.ProEtale

end EtaleComparison

namespace AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))
attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek supportShriekModelComparison supportFirstModelComparison
  supportThirdModelComparison supportSheafAdjunction supportDerivedAdjunction
end AlgebraicGeometry.ProEtale
