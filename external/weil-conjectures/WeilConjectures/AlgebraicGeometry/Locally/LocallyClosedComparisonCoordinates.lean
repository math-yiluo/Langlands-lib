/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedExtensionComparison
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Locally closed exceptional comparison with its adjunction normalization

## References

* Stacks 0GJ1
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Coordinates for the two ambient closed right adjoints. Each functor is determined
up to the unique counit-compatible adjoint isomorphism, rather than freely chosen data. -/
structure LocallyClosedComparisonAdjoints (A : Type (u + 1)) [CommRing A]
    {S V : Scheme.{u}} (c : S ⟶ V) where
  etale : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  proetale : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))
  etaleAdjunction : (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⊣ etale
  proetaleAdjunction : (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⊣ proetale

/-- The etale closed-then-open extension on ordinary derived categories. -/
abbrev locallyClosedEtaleExtension (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The pro-etale closed-then-open extension on ordinary derived categories. -/
abbrev locallyClosedProEtaleExtension (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

namespace LocallyClosedComparisonAdjoints

variable {A : Type (u + 1)} [CommRing A] {S V T : Scheme.{u}} {c : S ⟶ V}

/-- Open restriction followed by the ambient closed etale right adjoint. -/
abbrev etaleRight (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] :=
  (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ a.etale

/-- Open restriction followed by the ambient closed pro-etale right adjoint. -/
abbrev proetaleRight (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] :=
  (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ a.proetale

/-- The literal pasted etale adjunction, fixing its unit and counit. -/
def etalePasted (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] : locallyClosedEtaleExtension A c v ⊣ a.etaleRight v :=
  a.etaleAdjunction.comp
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction

/-- The literal pasted pro-etale adjunction, fixing its unit and counit. -/
def proetalePasted (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] : locallyClosedProEtaleExtension A c v ⊣ a.proetaleRight v :=
  a.proetaleAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction

end LocallyClosedComparisonAdjoints

/-- Delta is the specified closed counit mate followed by open extension comparison. -/
def locallyClosedExtensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    DerivedCategory.Plus.ι ⋙ locallyClosedEtaleExtension A c v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        locallyClosedProEtaleExtension A c v :=
  Functor.isoWhiskerLeft
      (DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor)
      (Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v)
        (comparisonUpperStar (ModuleCat.{u + 1} A) T) ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) v) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
    Functor.isoWhiskerRight (fixedDirectImageComparisonIso A c)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The scheme-theoretic closure compactification of an immersion. No density or
nonemptiness assumption is imposed. -/
def locallyClosedImageCompactification {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s] : Compactification s where
  Z := s.image
  i := s.toImage
  g := s.imageι
  comm := s.toImage_imageι.symm
  isOpenImmersion := inferInstance
  isProper := inferInstance

/-- The unique identity-on-the-source sheaf comparison, oriented from closed/open
extension to closure extension. The existing theorem specifies uniqueness by the open
unit and closed counit, so this choice cannot introduce a scalar twist. -/
def locallyClosedEtaleSheafIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    Etale.lowerStar (ModuleCat.{u + 1} A) c ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (c ≫ v).toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v).imageι :=
  (((((etale_locallyClosed_extension_comparison (A := A) T (𝟙 T) v).2 (c ≫ v)).choose_spec).1
    c v rfl).choose).symm

/-- The normalized identification with etale compact support at the closure
compactification. Both closed direct images are exact; the comparison is the
localization of the preceding uniquely normalized sheaf map. -/
def locallyClosedEtaleSupportIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    locallyClosedEtaleExtension A c v ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (locallyClosedImageCompactification (c ≫ v)) := by
  dsimp only [Etale.rightDerivedLowerShriekOfCompactification, locallyClosedImageCompactification]
  exact Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (locallyClosedEtaleSheafIso A c v) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      ((Etale.lowerStar (ModuleCat.{u + 1} A)
        (c ≫ v).imageι).rightDerivedFunctorIsoMapDerivedCategory).symm

/-- The existing Brown-adjoint theorem at the closure compactification. The
Noetherian and compact hypotheses it needs follow from the immersion into T; they
are constructed here rather than imposed on the statement as additional assumptions. -/
instance locallyClosedImage_isLeftAdjoint (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsNoetherian T] :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (locallyClosedImageCompactification s)).IsLeftAdjoint :=
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace s
  letI : IsLocallyNoetherian s.image := LocallyOfFiniteType.isLocallyNoetherian s.imageι
  letI : CompactSpace s.image := QuasiCompact.compactSpace_of_compactSpace s.imageι
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (locallyClosedImageCompactification s)

/-- The ordinary etale exceptional right adjoint in closure coordinates. -/
abbrev locallyClosedEtaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsNoetherian T] :=
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (locallyClosedImageCompactification s)).rightAdjoint

/-- The counit-compatible etale adjoint identification induced by the normalized
left-adjoint comparison, with no independently chosen right-adjoint isomorphism. -/
def locallyClosedEtaleRightIso {A : Type (u + 1)} [CommRing A] [Finite A]
    {S V T : Scheme.{u}} {c : S ⟶ V} (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)]
    (a : LocallyClosedComparisonAdjoints A c) :
    a.etaleRight v ≅ locallyClosedEtaleExceptional A (c ≫ v) :=
  (a.etalePasted v).rightAdjointUniq
    ((Adjunction.ofIsLeftAdjoint _).ofNatIsoLeft (locallyClosedEtaleSupportIso A c v).symm)

end AlgebraicGeometry.ProEtale
