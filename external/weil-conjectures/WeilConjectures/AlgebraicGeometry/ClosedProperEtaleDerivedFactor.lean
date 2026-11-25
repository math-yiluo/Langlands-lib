/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStarClopen
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Clopen-factor normalization on the etale site

Source: the ordered composition and comparison paragraphs of
sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The direct-image factorization through the actual clopen part of the compactification. -/
def properEtaleModelComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  letI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range B c.i
    c.i.isClosedEmbedding.isClosed_range
  letI := (upperStarLowerStarAdjunction B c.i).preservesKInjectiveComplexes
  exact Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (asIso (openImmersionLowerShriekToLowerStar B c.i)) ≪≫
        (lowerStar B c.i).rightDerivedFunctorIsoMapDerivedCategory.symm) _ ≪≫
    Functor.rightDerivedFunctorCompIso' (lowerStar B c.i) (lowerStar B c.g)
      (lowerStarComp B c.i c.g f c.comm)

/-- The canonical etale proper comparison is the clopen direct-image model.
Source: blueprint latest, sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, composition and comparison;
parent proof Step 3 (blueprint: lem-pur-closed-proper-etale-derived-factor).

Proof: write c=(j,p) for the chosen compactification of f. Properness makes j clopen,
so j_!, j^* and j_* are exact and j_!→j_* is an isomorphism. At the sheaf level,
the unit of j_!⊣j^*, followed by j^*(j_!→j_*) and the counit of j^*⊣j_*, is the
identity. Apply the exact localization to this equality. The unit and counit
factorization equations on homotopy representatives show that the resulting
adjunctions are precisely the published derived adjunctions, with Rj_* identified
with D(j_*). Therefore D(j_!→j_*) followed by the inverse exact comparison is the
adjunct of the inverse open unit. This is the definition of the published derived
open forget-supports map. Whisker by Rp_*. The adjunction-defined ordinary compositor
is the generic derived compositor by its conjugate-unit formula; naturality in the
underived equality c.comm identifies the final transport with the generic compositor
for lowerStarComp B c.i c.g f c.comm. The resulting composite is
properEtaleModelComparison. Empty clopen parts, identities and zero rings obey the
same triangle identities, so no extra geometric hypothesis is required. -/
theorem closedProperEtaleDerivedFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f] :
    rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f =
      properEtaleModelComparison A f := by
  apply Iso.ext
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom, rightDerivedLowerShriekToLowerStarComp,
    rightDerivedLowerStarComp_hom_comp_congr_hom_eq_compIso',
    derivedOpenImmersionLowerShriekToLowerStar_eq_of_isClosedImmersion]
  rfl
end AlgebraicGeometry.Etale
