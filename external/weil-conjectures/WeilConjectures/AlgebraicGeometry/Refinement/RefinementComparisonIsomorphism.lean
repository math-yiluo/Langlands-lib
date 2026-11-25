/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
/-!
# Refinement comparison with an explicit etale-origin witness

The recorded witness uses modules over the continuous-function coefficient sheaf.
The recorded compact-support candidate uses fixed scalar module sheaves. We evaluate
it on the canonical inverse realization of the same object. The witness is transported
through that equivalence using its unit and the exact-functor composition isomorphism.

## References

* Stacks 0F7I, part (b)
* Stacks 0F7I, canonical inclusion of D-plus
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical change between the two recorded coefficient presentations, derived
termwise from the existing coefficient realization equivalence. -/
def refinementCoefficientEquivalence (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) ≌
      FiniteCoefficientDerivedCategory T Λ :=
  (finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence

/-- The underlying object in the fixed scalar presentation of the recorded compact-support
candidate. This is the canonical inverse realization of `K`, retaining no new choice. -/
def refinementFixedObject (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (O : EtaleOriginDerivedCategory T Λ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) :=
  (refinementCoefficientEquivalence T Λ).inverse.obj O.1.obj

/-- The retained witness in the fixed scalar presentation. Starting with `nu^* L`, insert
inverse realization after realization via the equivalence unit, then transport the actual
retained `alpha`. The composition and bounded below inclusion comparisons are canonical. -/
def refinementFixedWitnessIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (O : EtaleOriginDerivedCategory T Λ) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj O.2.L.obj ≅
      refinementFixedObject T Λ O :=
  let e := refinementCoefficientEquivalence T Λ
  e.unitIso.app _ ≪≫ e.inverse.mapIso
    (((Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
      (finiteCoefficientRealization T Λ)).app O.2.L.obj) ≪≫
      ((finiteCoefficientComparison T Λ).mapDerivedCategoryPlusCompatibility.app O.2.L).symm ≪≫
      DerivedCategory.Plus.ι.mapIso O.2.alpha)

/-- Part (a): `j₂!(alpha)⁻¹`, followed by the canonical proper-open comparison for `L`,
followed by `Ru_* j₁!(alpha)`. The order here is Lean's left-to-right composition order. -/
def refinementProperOpenIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (O : EtaleOriginDerivedCategory X Λ) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₂.i).mapDerivedCategory.obj
        (refinementFixedObject X Λ O) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) r.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.obj
          (refinementFixedObject X Λ O)) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₂.i).mapDerivedCategory.mapIso
      (refinementFixedWitnessIso X Λ O).symm ≪≫
    properOpenProEtaleIso Λ r.hom c₁.i c₂.i r.i_hom O.2.L ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) r.hom).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.mapIso
        (refinementFixedWitnessIso X Λ O))

/-- Part (b): the canonical direct-image compositor at `j₁!K`, followed by the ambient
proper direct image of the inverse of part (a). The factorization equality is exactly
`r.hom_g`; no Cartesian-square assumption on `r` is used. -/
def refinementComparisonAtWitness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (O : EtaleOriginDerivedCategory X Λ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₁).obj
        (refinementFixedObject X Λ O) ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₂).obj
        (refinementFixedObject X Λ O) :=
  ((eqToIso (congrArg
      (fun q ↦ (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor)
      r.hom_g.symm)).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.obj
          (refinementFixedObject X Λ O))) ≪≫
    (finiteDirectImageComposition Λ r.hom c₂.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.obj
        (refinementFixedObject X Λ O)) ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) c₂.g).rightDerivedFunctor.mapIso
      (refinementProperOpenIso Λ r O).symm

/-- Positive-level coefficient specialization of the witness category. `ULift` places the
coefficient ring in the site's coefficient universe; its discrete topology is explicit. -/
abbrev RefinementFiniteLevelOrigin (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) :=
  @EtaleOriginDerivedCategory X (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) _
    ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
      Padic.coefficientExtensionRing l E n).finite_iff.mpr
        (Padic.finite_coefficientExtensionRing l E n hn)) ⊥ (discreteTopology_bot _)

/-- The retained finite-level object in the canonical fixed scalar presentation. -/
def refinementFiniteLevelFixedObject (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) (O : RefinementFiniteLevelOrigin l E n hn X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  refinementFixedObject X (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) O

/-- The comparison isomorphism along a refinement at positive finite coefficient level,
for separated finite-type morphisms between finite-type schemes over the field `K₀`.
The value in the fixed scalar presentation is the canonical inverse realization of the
retained `K`. The definition is objectwise and makes no naturality, witness-independence,
identity-refinement, or composition-law assertion. -/
def refinementComparisonIsomorphism (K₀ : Type u) [Field K₀]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : K₀))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (O : RefinementFiniteLevelOrigin l E n hn X) :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) c₁).obj
        (refinementFiniteLevelFixedObject l E n hn X O) ≅
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) c₂).obj
          (refinementFiniteLevelFixedObject l E n hn X O) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  refinementComparisonAtWitness (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) r O

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Transport proper direct image by equality of scheme maps, without comparing
large derived functor structures when the equality transport is evaluated. -/
def properTransportDirectImageCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus ≅
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus := by
  subst g
  exact Iso.refl _

omit [Finite A] in
/-- Equality transport is the identity for a reflexive equality. -/
@[simp]
theorem properTransportDirectImageCongr_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    properTransportDirectImageCongr A (rfl : f = f) = Iso.refl _ := rfl

/-- The actual refinement arrow on bounded-below comparison inputs: the direct-image
compositor followed by the proper image of the inverse specified proper/open arrow.
It is meaningful for every refinement, including noncartesian refinements. -/
def properTransportRefinementPlus {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (properTransportDirectImageCongr A r.hom_g.symm).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≪≫
    (proEtaleComparisonDirectImageCompIso A r.hom d.g).symm.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus.mapIso
      (properOpenProEtaleIsoPlus A r.hom c.i d.i r.i_hom L).symm

/-- The same actual refinement arrow in the ambient derived category. -/
def properTransportRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.app
        L).symm ≪≫
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (properTransportRefinementPlus A r L) ≪≫
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.app L)

end AlgebraicGeometry.ProEtale
