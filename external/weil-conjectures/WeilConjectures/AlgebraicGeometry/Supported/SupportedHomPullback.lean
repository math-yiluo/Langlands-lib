/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Module.ModuleSupportedHomTransport
import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import all WeilConjectures.AlgebraicGeometry.Support.SupportQuotientPairPullback
import all WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison

/-!
# Supported Hom and pullback of closed pairs

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and Example 9.5,
pp. 66--67; the kernel-of-restriction construction and its pullback functoriality
(blueprint: lem-pur-supported-hom-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace AlgebraicGeometry

/-- Site data used to spell out the same normalized identification in both topologies.
The site, restriction arrow, supported constant, and its actual restriction map are data,
not a replacement definition of supported sections.
Source: Milne, Section 9, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
structure SupportHomPair (A : Type (u + 1)) [CommRing A] where
  Site : Type (u + 1)
  [category : Category.{u} Site]
  topology : GrothendieckTopology Site
  [sheafify : HasSheafify topology (ModuleCat.{u + 1} A)]
  [grothendieck : IsGrothendieckAbelian.{u + 1}
    (Sheaf topology (ModuleCat.{u + 1} A))]
  terminal : Site
  isTerminal : IsTerminal terminal
  complement : Site
  restriction : complement ⟶ terminal
  supported : Sheaf topology (ModuleCat.{u + 1} A)
  constantRestriction :
    (constantSheaf topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ supported

attribute [instance] SupportHomPair.category SupportHomPair.sheafify SupportHomPair.grothendieck

namespace SupportHomPair

variable {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)

/-- The already defined support kernel in the given pair.
Source: Milne, Section 9 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev sections :=
  Sheaf.supportedSectionsFunctor S.topology (ModuleCat.{u + 1} A) S.restriction

/-- The degree-a cohomology of the published bounded-below right derived support functor.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev group (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :=
  (Sheaf.supportHypercohomologyFunctor S.topology
    (ModuleCat.{u + 1} A) S.restriction a).obj K

/-- Termwise support on an injective representative, using the existing kernel functor.
Source: Milne, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
abbrev complex (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) :=
  (S.sections.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj

/-- Image of a supported cocycle under the canonical right-derived-unit comparison.
Source: Milne, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
def cycleClass (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ) (x : (S.complex I).cycles a) :
    S.group (DerivedCategory.Plus.Q.obj I) a :=
  (Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) S.sections I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom ((S.complex I).homologyπ a x)

/-- Derived morphisms from the supported single object, with the original integer shift.
This names the existing Hom type, so checking its users does not repeatedly compute
that type's universe through the chosen derived-category localization.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev derivedHom
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :
    Type (u + 1) :=
  (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
    S.supported ⟶ K.obj⟦a⟧

/-- The localized map defined by a Hom cocycle, with the canonical cochain shift.
Source: Stacks 06XR, 070I; Milne, Ext proof
(blueprint: lem-pur-supported-hom-pullback). -/
def cocycleMorphism
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
      S.supported ⟶ (DerivedCategory.Plus.Q.obj I).obj⟦a⟧ :=
  supportedHomLocalizedCocycle I.obj a f hf ≫
    ((DerivedCategory.Plus.QCompιIso _).inv.app I)⟦a⟧'

/-- The normalized supported-Hom identification. The cocycle clause fixes its value by
`f ↦ (f ρ)(1)` on every injective representative, so no arbitrary natural isomorphism
can satisfy this interface. Its source is the actual derived support group.
Source: Milne, Theorem 9.4, Example 9.5 and Ext proof
(blueprint: lem-pur-supported-hom-pullback). -/
structure Identification where
  chi : SupportedHomChi S.topology A S.restriction S.supported
  naturality : SupportedHomChiNatural S.topology A S.restriction S.supported chi
  normalization : ∀ (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
      [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
      (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0)
      (x : (S.complex I).cycles a),
    kernel.ι ((I.obj.X a).obj.map S.restriction.op) ((S.complex I).iCycles a x) =
      ((constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _
        (S.constantRestriction ≫ f)) 1 →
      chi (DerivedCategory.Plus.Q.obj I) a (S.cycleClass I a x) =
        S.cocycleMorphism I a f hf

end SupportHomPair

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Constant restriction along a continuous site functor: sheafify the constant
presheaf unit and then restrict it. This sends each scalar to that same constant scalar.
Source: Milne, Example 9.5 (blueprint: lem-pur-supported-hom-pullback). -/
def supportHomConstantDirectImage {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify J' (ModuleCat.{u + 1} A)]
    (B : C ⥤ D) [B.IsContinuous J J'] :
    (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').obj
        ((constantSheaf J' (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :=
  ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    (Functor.whiskerLeft B.op
      (toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))))

namespace SupportHomPair

variable {A : Type (u + 1)} [CommRing A] (S T : SupportHomPair A)
variable (B : S.Site ⥤ T.Site) [hB : B.IsContinuous S.topology T.topology]
variable (L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
  Sheaf T.topology (ModuleCat.{u + 1} A))
variable (adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology)

/-- The three canonical comparisons used in the statement, in one interface.
`constantIso` is fixed by its adjoint constant sections, `closedIso` by the epic
constant restriction, and `supportUnit` by its kernel inclusion. The terminal and open
arrows are actual site arrows, so the last formula is the unit-induced section map.
Source: Milne, Theorem 9.4, Ext proof and kernel construction
(blueprint: lem-pur-supported-hom-pullback). -/
structure Transport where
  terminalMap : T.terminal ⟶ B.obj S.terminal
  complementMap : T.complement ⟶ B.obj S.complement
  restriction_square : complementMap ≫ B.map S.restriction = T.restriction ≫ terminalMap
  constantIso :
    L.obj ((constantSheaf S.topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) ≅
      (constantSheaf T.topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
  constantIso_spec : adj.homEquiv _ _ constantIso.hom =
    supportHomConstantDirectImage S.topology T.topology B
  closedIso : L.obj S.supported ≅ T.supported
  closedIso_spec : L.map S.constantRestriction ≫ closedIso.hom =
    constantIso.hom ≫ T.constantRestriction
  supportUnit : S.sections ⟶ L ⋙ T.sections
  supportUnit_spec : ∀ F : Sheaf S.topology (ModuleCat.{u + 1} A),
    supportUnit.app F ≫ kernel.ι ((L.obj F).obj.map T.restriction.op) =
      kernel.ι (F.obj.map S.restriction.op) ≫
        (adj.unit.app F).hom.app (op S.terminal) ≫ (L.obj F).obj.map terminalMap.op

variable {S T B L adj}

variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The actual derived kernel pullback, through the existing right-derived base-change
construction; it does not assume inverse image preserves injectives.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-supported-hom-pullback). -/
def Transport.derivedMap (e : Transport S T B L adj) :
    S.sections.rightDerivedFunctorPlus ⟶
      L.mapDerivedCategoryPlus ⋙ T.sections.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := S.sections) (G' := T.sections) (β := L) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ e.supportUnit)

/-- Pull a derived Hom back and precompose with closed exchange inverse, with the
published single-object and shift comparisons.
Source: Milne, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
def Transport.homMap (e : Transport S T B L adj)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :
    (f : S.derivedHom K a) → T.derivedHom (L.mapDerivedCategoryPlus.obj K) a :=
  Functor.representableTransportHom L e.closedIso K a

/-- The displayed equality for every supported class in the indicated coefficient object.
Source: Milne, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-supported-hom-pullback). -/
def Transport.Compatible (e : Transport S T B L adj)
    (chi : S.Identification) (chi' : T.Identification)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) : Prop :=
  moduleSupportedHomCompatible S.topology T.topology S.restriction T.restriction
    S.supported T.supported chi.chi chi'.chi L e.closedIso e.derivedMap K a

end SupportHomPair

/-- The etale pair uses the recorded scheme site, open complement, underived direct
image and constant sheaf. Source: Milne, Section 9
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev etaleSupportHomPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    SupportHomPair P.Coefficient where
  Site := X.Etale
  topology := X.smallEtaleTopology
  terminal := Scheme.Etale.mk (𝟙 X)
  isTerminal := MorphismProperty.Over.mkIdTerminal _ _
  complement := Scheme.Etale.mk i.openComplement.ι
  restriction := Etale.supportRestrictionArrow i
  supported := (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z)
  constantRestriction := by
    letI : (MorphismProperty.Over.pullback @Etale ⊤ i).IsContinuous
        X.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback i
    exact supportHomConstantDirectImage X.smallEtaleTopology Z.smallEtaleTopology
      (MorphismProperty.Over.pullback @Etale ⊤ i)

/-- The identical kernel construction in the pro-etale topology, with its ordinary
constant module. Source: Milne, Section 9 and the pro-etale supported-Hom node
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev proEtaleSupportHomPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    SupportHomPair P.Coefficient where
  Site := X.ProEt
  topology := Scheme.ProEt.topology X
  terminal := Scheme.ProEt.mk (𝟙 X)
  isTerminal := MorphismProperty.Over.mkIdTerminal _ _
  complement := Scheme.ProEt.mk i.openComplement.ι
  restriction := ProEtale.supportRestrictionArrow i
  supported := (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)
  constantRestriction := by
    letI := Scheme.ProEt.isContinuous_overPullback i
    exact supportHomConstantDirectImage (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
          (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z).inv

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Etale inverse image and its actual adjunction in the normalized transport interface.
Source: Milne, Section 9 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev etaleSupportHomTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) : Type (u + 2) := by
  letI : (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
      (etaleSupportHomPair P i).topology (etaleSupportHomPair P i').topology :=
    Etale.isContinuous_overPullback h
  exact SupportHomPair.Transport (etaleSupportHomPair P i) (etaleSupportHomPair P i')
    (MorphismProperty.Over.pullback @Etale ⊤ h)
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) h)

/-- Pro-etale inverse image and its actual adjunction, on the original small sites.
Source: Milne, Section 9; pro-etale constant presentation
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev proEtaleSupportHomTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) : Type (u + 2) := by
  letI : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).IsContinuous
      (proEtaleSupportHomPair P i).topology (proEtaleSupportHomPair P i').topology :=
    Scheme.ProEt.isContinuous_overPullback h
  exact SupportHomPair.Transport (proEtaleSupportHomPair P i) (proEtaleSupportHomPair P i')
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) h)

/-- The comparison inverse image and its actual adjunction in the same interface.
Source: Milne, Section 9; Stacks 099R
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev siteSupportHomTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Type (u + 2) := by
  letI : (Scheme.toProEt X).IsContinuous
      (etaleSupportHomPair P i).topology (proEtaleSupportHomPair P i).topology :=
    Scheme.isContinuous_toProEt X
  exact SupportHomPair.Transport (etaleSupportHomPair P i) (proEtaleSupportHomPair P i)
    (Scheme.toProEt X)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X)

/-- The published comparison of the two composite pullbacks, restricted canonically to D+.
Source: blueprint comparison-pullback coherence; Stacks 099R
(blueprint: lem-pur-supported-hom-pullback). -/
def supportHomDerivedComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X : Scheme.{u}} (h : X' ⟶ X) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategoryPlus ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X')).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (F := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X')
      (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
      (ProEtale.supportSiteComparisonCoefficientPullbackIso
        (ModuleCat.{u + 1} P.Coefficient) h) ≪≫
    Functor.mapDerivedCategoryPlusCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)

/-- Site comparison commutes with supported pullback and with the supported-constant
exchange. The first equation is in the actual derived support objects; the second uses
exactly the published inverse-image comparison, evaluated on the supported constant.
Source: Milne, Ext proof; blueprint affine-line orientation, etale-origin transport
(blueprint: lem-pur-supported-hom-pullback). -/
def SupportHomSquareCoherent (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X)
    (e : etaleSupportHomTransport P i i' h) (p : proEtaleSupportHomTransport P i i' h)
    (v : siteSupportHomTransport P i) (v' : siteSupportHomTransport P i') : Prop :=
  (∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    (v.derivedMap (hB := Scheme.isContinuous_toProEt X)).app K ≫
      (p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback h)).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj K) =
      (e.derivedMap (hB := Etale.isContinuous_overPullback h)).app K ≫
        (v'.derivedMap (hB := Scheme.isContinuous_toProEt X')).app
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj K) ≫
        (proEtaleSupportHomPair P i').sections.rightDerivedFunctorPlus.map
          ((supportHomDerivedComparison P h).hom.app K)) ∧
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').map
      (e.closedIso (hB := Etale.isContinuous_overPullback h)).hom ≫
      (v'.closedIso (hB := Scheme.isContinuous_toProEt X')).hom =
    (ProEtale.supportSiteComparisonCoefficientPullbackIso
      (ModuleCat.{u + 1} P.Coefficient) h).hom.app (etaleSupportHomPair P i).supported ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).map
          (v.closedIso (hB := Scheme.isContinuous_toProEt X)).hom ≫
          (p.closedIso (hB := Scheme.ProEt.isContinuous_overPullback h)).hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance supportHomEtaleContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f

/-- An identity resolution and identity comparison leave the localized cocycle unchanged. -/
private theorem supportHomIdentityRoof
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) {K : C} {T : E}
    (v : (K ≅ K) → (T ⟶ G.obj (F.obj K)))
    (r f : T ⟶ G.obj (F.obj K)) (hf : r = f)
    (e : K ≅ K) (q : F.obj K ⟶ F.obj K)
    (he : e = Iso.refl K) (hq : q = 𝟙 _)
    (h : v e.symm = r ≫ G.map q ≫ G.map (F.map e.inv)) :
    v (Iso.refl K) = f := by
  subst e q f
  change v (Iso.refl K) = r ≫ G.map (𝟙 _) ≫ G.map (F.map (𝟙 _)) at h
  simpa only [F.map_id, G.map_id, Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def supportHomIdentificationOfNormalization
    {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction) : S.Identification where
  chi := N.chi
  naturality := N.naturality
  normalization := by
    as_aux_lemma =>
      intro I hi a f hf x hx
      obtain ⟨g, ⟨hg, hgf⟩, _⟩ := N.cocycle I I (𝟙 I) a x
      have hfg : f = g := by
        apply (AddCommGrpCat.mono_iff_injective (N.theta.hom.app (I.obj.X a))).mp inferInstance
        apply (ModuleCat.mono_iff_injective
          (kernel.ι ((I.obj.X a).obj.map S.restriction.op))).mp inferInstance
        rw [N.evaluation, hg]
        exact hx.symm
      subst g
      obtain ⟨hg, heq⟩ := hgf
      have hid : supportedHomResolutionIso S.topology A I I (𝟙 I) = Iso.refl _ := by
        apply Iso.ext
        apply DerivedCategory.Plus.ι.map_injective
        change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
        rw [Functor.map_preimage]
        simp [DerivedCategory.Plus.QCompιIso_hom_app,
          DerivedCategory.Plus.QCompιIso_inv_app]; rfl
      let G := shiftFunctor (DerivedCategory (Sheaf S.topology (ModuleCat.{u + 1} A))) a
      let r : S.derivedHom (DerivedCategory.Plus.Q.obj I) a :=
        supportedHomLocalizedCocycle I.obj a f hf
      have hnorm := supportHomIdentityRoof DerivedCategory.Plus.ι G
        (fun d ↦ N.chi (DerivedCategory.Plus.Q.obj I) a
          ((Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) S.sections I
            (DerivedCategory.Plus.Q.obj I) d a).hom ((S.complex I).homologyπ a x)))
        r r rfl (supportedHomResolutionIso S.topology A I I (𝟙 I))
        ((DerivedCategory.Plus.QCompιIso
          (Sheaf S.topology (ModuleCat.{u + 1} A))).inv.app I) hid (by rfl) heq
      have hqh : G.map ((DerivedCategory.Plus.QCompιIso
          (Sheaf S.topology (ModuleCat.{u + 1} A))).inv.app I) = 𝟙 _ := by
        change G.map (𝟙 _) = 𝟙 _
        exact G.map_id _
      change _ = r ≫ G.map ((DerivedCategory.Plus.QCompιIso
        (Sheaf S.topology (ModuleCat.{u + 1} A))).inv.app I)
      exact hnorm.trans ((congrArg (fun t => r ≫ t) hqh).trans (Category.comp_id r)).symm

private theorem supportHomIdentificationOfNormalization_chi
    {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction) :
    (supportHomIdentificationOfNormalization S N).chi = N.chi := by
  with_unfolding_all rfl

private theorem supportHomConstantEvaluation
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} A))
    (f : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    (constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _ f =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T) ≫
        f.hom.app (op T) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomConstantDirectImage_evaluation
    {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify J' (ModuleCat.{u + 1} A)]
    (B : C ⥤ D) [B.IsContinuous J J']
    {T : C} (hT : IsTerminal T) {T' : D} (hT' : IsTerminal T')
    (t : T' ⟶ B.obj T) (M : Sheaf J' (ModuleCat.{u + 1} A))
    (f : (constantSheaf J' (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    (constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _
        (supportHomConstantDirectImage J J' B ≫
          (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').map f) ≫
        M.obj.map t.op =
      (constantSheafAdj J' (ModuleCat.{u + 1} A) hT').homEquiv _ _ f := by
  rw [supportHomConstantEvaluation, supportHomConstantEvaluation]
  have he : (sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _
      (supportHomConstantDirectImage J J' B ≫
        (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').map f) =
      Functor.whiskerLeft B.op
        (toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A)) ≫ f.hom) := by
    rw [Adjunction.homEquiv_naturality_right]
    erw [Equiv.apply_symm_apply]
    rfl
  have ht := congr_app he (op T)
  change (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T) ≫
      (supportHomConstantDirectImage J J' B ≫
        (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').map f).hom.app (op T) =
    (toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))).app (op (B.obj T)) ≫
      f.hom.app (op (B.obj T)) at ht
  rw [ht]
  simpa using ((toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A)) ≫
    f.hom).naturality t.op).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomEvaluationInverseImage
    {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
    {B : S.Site ⥤ T.Site} [B.IsContinuous S.topology T.topology]
    {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.topology (ModuleCat.{u + 1} A)}
    {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
    (e : SupportHomPair.Transport S T B L adj)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (f : (constantSheaf S.topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    (constantSheafAdj T.topology (ModuleCat.{u + 1} A) T.isTerminal).homEquiv _ _
        (e.constantIso.inv ≫ L.map f) =
      (constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _ f ≫
        (adj.unit.app M).hom.app (op S.terminal) ≫
        (L.obj M).obj.map e.terminalMap.op := by
  let R := B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology
  have hf : f ≫ adj.unit.app M =
      supportHomConstantDirectImage S.topology T.topology B ≫
        R.map (e.constantIso.inv ≫ L.map f) := by
    rw [← e.constantIso_spec, Adjunction.homEquiv_unit]
    simp only [R, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, e.constantIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact adj.unit.naturality f
  have he := supportHomConstantDirectImage_evaluation S.topology T.topology B
    S.isTerminal T.isTerminal e.terminalMap (L.obj M) (e.constantIso.inv ≫ L.map f)
  rw [← hf, Adjunction.homEquiv_naturality_right] at he
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomEvaluationSquare
    {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
    {B : S.Site ⥤ T.Site} [B.IsContinuous S.topology T.topology]
    {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.topology (ModuleCat.{u + 1} A)}
    {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
    (e : SupportHomPair.Transport S T B L adj)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction)
    (N' : SupportedHomCocycleNormalization T.topology A T.isTerminal T.restriction
      T.supported T.constantRestriction)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A)) (f : S.supported ⟶ M) :
    N'.theta.hom.app (L.obj M) (e.closedIso.inv ≫ L.map f) =
      e.supportUnit.app M (N.theta.hom.app M f) := by
  apply (ModuleCat.mono_iff_injective
    (kernel.ι ((L.obj M).obj.map T.restriction.op))).mp inferInstance
  rw [N'.evaluation]
  have hrho : T.constantRestriction ≫ e.closedIso.inv =
      e.constantIso.inv ≫ L.map S.constantRestriction := by
    apply (cancel_mono e.closedIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [e.closedIso_spec, Iso.inv_hom_id_assoc]
  have hunit := (ConcreteCategory.congr_hom (e.supportUnit_spec M)
    (N.theta.hom.app M f)).symm
  change _ = kernel.ι ((L.obj M).obj.map T.restriction.op)
    (e.supportUnit.app M (N.theta.hom.app M f)) at hunit
  rw [← hunit]
  have he := ConcreteCategory.congr_hom (supportHomEvaluationInverseImage e M
    (S.constantRestriction ≫ f)) 1
  simp only [Functor.map_comp] at he
  rw [← Category.assoc, ← hrho] at he
  change _ = (L.obj M).obj.map e.terminalMap.op
    ((adj.unit.app M).hom.app (op S.terminal)
      (((constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _
        (S.constantRestriction ≫ f)) 1)) at he
  change _ = (L.obj M).obj.map e.terminalMap.op
    ((adj.unit.app M).hom.app (op S.terminal)
      (kernel.ι (M.obj.map S.restriction.op) (N.theta.hom.app M f)))
  rw [N.evaluation]
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomEtaleConstantIso_spec
    {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
        Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
          (ModuleCat.of A A)).hom =
      supportHomConstantDirectImage Y.smallEtaleTopology X.smallEtaleTopology
        (MorphismProperty.Over.pullback @Etale ⊤ f) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let a := ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).comp adj).ofNatIsoRight
    (Etale.lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) f)
  let b := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  apply ((adj.homEquiv _ _).symm).injective
  rw [Equiv.symm_apply_apply]
  apply (a.homEquiv _ _).injective
  rw [Scheme.upperStarConstantSheafIso]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  symm
  simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ (supportHomConstantDirectImage _ _ _) ≫
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A)).obj.map (PreservesTerminal.iso f.Etale).inv.op = _
  have he := supportHomConstantDirectImage_evaluation Y.smallEtaleTopology X.smallEtaleTopology
    f.Etale terminalIsTerminal terminalIsTerminal
    (PreservesTerminal.iso f.Etale).inv
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at he
  conv_rhs at he =>
    rw [Adjunction.homEquiv_unit]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomGlobalEvaluation
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] [HasTerminal C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasGlobalSectionsFunctor J (ModuleCat.{u + 1} A)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} A))
    (f : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    (constantSheafΓAdj J (ModuleCat.{u + 1} A)).homEquiv _ _ f ≫
        (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} A) hT).hom.app M =
      (constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _ f := by
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [(Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} A) hT).hom.naturality]
  simp only [Sheaf.ΓNatIsoSheafSections, Adjunction.unit_rightAdjointUniq_hom_app_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomProEtaleConstantIso_spec
    {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := Scheme.ProEt.isContinuous_overPullback f
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        ((ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).app
          (ModuleCat.of A A)).hom =
      supportHomConstantDirectImage (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) := by
  let := Scheme.ProEt.isContinuous_overPullback f
  change (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      ((ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        (ModuleCat.of A A)) = _
  rw [ProEtale.CachedConstantCoherence.proConstant_eq_inverse,
    Scheme.constantInverse]
  erw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomComparisonConstantIso_spec
    {A : Type (u + 1)} [CommRing A] (X : Scheme.{u}) :
    letI := Scheme.isContinuous_toProEt X
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _
        (ProEtale.comparisonUpperStarUnitIso A X).hom =
      supportHomConstantDirectImage X.smallEtaleTopology (Scheme.ProEt.topology X)
        (Scheme.toProEt X) := by
  let := Scheme.isContinuous_toProEt X
  let : (X.smallEtaleTopology.W (A := ModuleCat.{u + 1} A)).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  let : ((Scheme.ProEt.topology X).W (A := ModuleCat.{u + 1} A)).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  change (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X)
    (ModuleCat.{u + 1} A) X.smallEtaleTopology (Scheme.ProEt.topology X)).homEquiv _ _
    (Functor.OplaxMonoidal.η (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.toProEt X) (ModuleCat.{u + 1} A) X.smallEtaleTopology
      (Scheme.ProEt.topology X))) = _
  rw [Adjunction.leftAdjointOplaxMonoidal_η, Equiv.apply_symm_apply]
  apply ((sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  rw [supportHomConstantDirectImage]
  erw [Equiv.apply_symm_apply]
  have he := Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous
    (Scheme.toProEt X) (ModuleCat.{u + 1} A) X.smallEtaleTopology
    (Scheme.ProEt.topology X)
  have hJ : Functor.OplaxMonoidal.η
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) = 𝟙 _ := rfl
  have hK : Functor.OplaxMonoidal.η
      (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) = 𝟙 _ := rfl
  simp only [Adjunction.homEquiv_unit, Adjunction.rightAdjointLaxMonoidal_ε,
    hJ, hK] at he
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.comp_id] at he
  have hW : Functor.LaxMonoidal.ε
      ((Functor.whiskeringLeft X.Etaleᵒᵖ X.ProEtᵒᵖ (ModuleCat.{u + 1} A)).obj
        X.toProEt.op) = 𝟙 _ := rfl
  rw [hW] at he
  erw [Category.id_comp] at he
  exact he

private theorem supportHomComplement_le
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    i'.openComplement ≤ h ⁻¹ᵁ i.openComplement := by
  have hs := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  intro x hx
  change h x ∉ Set.range i at ⊢
  change x ∉ Set.range i' at hx
  rwa [Scheme.range_snd_of_isPullback hs] at hx

private def supportHomEtaleComplementMap
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    Scheme.Etale.mk i'.openComplement.ι ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ h).obj
        (Scheme.Etale.mk i.openComplement.ι) :=
  MorphismProperty.Over.homMk
    (pullback.lift (h.resLE _ _ (supportHomComplement_le i i' h g sq))
      i'.openComplement.ι (Scheme.Hom.resLE_comp_ι _ _))
    (pullback.lift_snd _ _ _)

private def supportHomProEtaleComplementMap
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    Scheme.ProEt.mk i'.openComplement.ι ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj
        (Scheme.ProEt.mk i.openComplement.ι) :=
  MorphismProperty.Over.homMk
    (pullback.lift (h.resLE _ _ (supportHomComplement_le i i' h g sq))
      i'.openComplement.ι (Scheme.Hom.resLE_comp_ι _ _))
    (pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def supportHomProEtaleSupportedIso
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (proEtaleSupportHomPair P i).supported ≅
      SupportedConstantNormalization.supported P.Coefficient true i :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapIso
    (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportHomProEtaleSupportedIso_spec
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (proEtaleSupportHomPair P i).constantRestriction ≫
        (supportHomProEtaleSupportedIso P i).hom =
      SupportedConstantNormalization.restriction P.Coefficient true i := by
  let := Scheme.ProEt.isContinuous_overPullback i
  change (supportHomConstantDirectImage (A := P.Coefficient) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
        (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z).inv) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
        (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z).hom = _
  simp only [Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rfl

private theorem supportHomCocycle_precomp.{uC, vC, wC}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B B' : C} (g : B' ⟶ B) (I : CochainComplex C ℤ) (a : ℤ)
    (f : B ⟶ I.X a) (hf : f ≫ I.d a (a + 1) = 0)
    (hgf : (g ≫ f) ≫ I.d a (a + 1) = 0) :
    supportedHomLocalizedCocycle I a (g ≫ f) hgf =
      (DerivedCategory.singleFunctor C 0).map g ≫
        supportedHomLocalizedCocycle I a f hf := by
  simp only [supportedHomLocalizedCocycle_eq]
  rw [Cocycle.fromSingleMk_precomp, Cocycle.equivHomShift_symm_precomp]
  · simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]
    rfl

private theorem supportHomCocycle_precomp_roof.{uC, vC, wC}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B B' : C} (g : B' ⟶ B) (I : CochainComplex C ℤ) (a : ℤ)
    (f : B ⟶ I.X a) (hf : f ≫ I.d a (a + 1) = 0)
    (hgf : (g ≫ f) ≫ I.d a (a + 1) = 0)
    (K : DerivedCategory C)
    (e : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj I ⟶ K) :
    (DerivedCategory.singleFunctor C 0).map g ≫
      (supportedHomLocalizedCocycle I a f hf ≫
          ((DerivedCategory.quotientCompQhIso C).inv.app I)⟦a⟧' ≫ e⟦a⟧') =
    supportedHomLocalizedCocycle I a (g ≫ f) hgf ≫
        ((DerivedCategory.quotientCompQhIso C).inv.app I)⟦a⟧' ≫ e⟦a⟧' := by
  rw [supportHomCocycle_precomp g I a f hf hgf]
  simp only [Category.assoc]

private def supportHomPrecompEquiv.{uC, vC}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {B B' : C} (d : B' ≅ B) (K : C) : (B ⟶ K) ≃+ (B' ⟶ K) where
  toFun f := d.hom ≫ f
  invFun f := d.inv ≫ f
  left_inv f := by simp only [Iso.inv_hom_id_assoc]
  right_inv f := by simp only [Iso.hom_inv_id_assoc]
  map_add' f g := Preadditive.comp_add _ _ _ _ _ _

section
variable {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    (B₀ : Sheaf J (ModuleCat.{u + 1} A))
    (rho₀ : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B₀)
    (B : Sheaf J (ModuleCat.{u + 1} A)) (d : B₀ ≅ B)
@[irreducible] private def supportHomChangeTheta
    (θ : SupportedHomEvaluationIso J A j B) :
    SupportedHomEvaluationIso J A j B₀ :=
  (preadditiveCoyoneda.mapIso d.op).symm ≪≫ θ
@[irreducible] private def supportHomChangeChi
    (χ : SupportedHomChi J A j B) :
    SupportedHomChi J A j B₀ := fun K a ↦
  (χ K a).trans (supportHomPrecompEquiv
    ((DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{u + 1} A)) 0).mapIso d)
      (K.obj⟦a⟧))

omit [HasSheafify J (ModuleCat.{u + 1} A)]
  [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))] in
private theorem supportHomChangeTheta_apply
    (θ : SupportedHomEvaluationIso J A j B)
    (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B₀ ⟶ M) :
    (supportHomChangeTheta J j B₀ B d θ).hom.app M f = θ.hom.app M (d.inv ≫ f) := by
  with_unfolding_all rfl
private theorem supportHomChangeChi_apply
    (χ : SupportedHomChi J A j B)
    (K : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) (a : ℤ)
    (x : (Sheaf.supportHypercohomologyFunctor J
      (ModuleCat.{u + 1} A) j a).obj K) :
    supportHomChangeChi J j B₀ B d χ K a x =
      (DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{u + 1} A)) 0).map d.hom ≫
        χ K a x := by
  with_unfolding_all rfl

private theorem supportHomChangeCocycle
    (θ : SupportedHomEvaluationIso J A j B)
    (χ : SupportedHomChi J A j B)
    (hcyc : SupportedHomChiCocycle J A j B θ χ) :
    SupportedHomChiCocycle J A j B₀
      (supportHomChangeTheta J j B₀ B d θ) (supportHomChangeChi J j B₀ B d χ) := by
  intro K I hi e he a x
  obtain ⟨f, ⟨hf, hfn⟩, _⟩ := hcyc K I e a x
  obtain ⟨hdf, hchi⟩ := hfn
  have hdcomp : (d.hom ≫ f) ≫ I.obj.d a (a + 1) = 0 := by
    exact (Category.assoc d.hom f (I.obj.d a (a + 1))).trans
      ((congrArg (fun k : B ⟶ I.obj.X (a + 1) ↦ d.hom ≫ k) hdf).trans
        (Limits.comp_zero))
  have heval : (supportHomChangeTheta J j B₀ B d θ).hom.app (I.obj.X a) (d.hom ≫ f) =
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A)
        j).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I.obj).iCycles a x := by
    rw [supportHomChangeTheta_apply, Iso.inv_hom_id_assoc]
    exact hf
  refine ⟨d.hom ≫ f, ⟨heval, ⟨hdcomp, ?_⟩⟩, ?_⟩
  · rw [supportHomChangeChi_apply, hchi]
    exact supportHomCocycle_precomp_roof.{u + 2, u + 1, u + 1}
      d.hom I.obj a f hdf hdcomp _
        (DerivedCategory.Plus.ι.map (supportedHomResolutionIso J A K I e).inv)
  · intro g hg
    apply (AddCommGrpCat.mono_iff_injective
      ((supportHomChangeTheta J j B₀ B d θ).hom.app (I.obj.X a))).mp inferInstance
    exact hg.1.trans heval.symm
end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def supportHomNormalizationChangeSupportedGeneric
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    (B₀ : Sheaf J (ModuleCat.{u + 1} A))
    (rho₀ : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B₀)
    (B : Sheaf J (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (d : B₀ ≅ B) (hd : rho₀ ≫ d.hom = rho)
    (N : SupportedHomCocycleNormalization J A hT j B rho) :
    SupportedHomCocycleNormalization J A hT j
      B₀ rho₀ := by
  exact
    { theta := supportHomChangeTheta J j B₀ B d N.theta
      evaluation := by
        intro M f
        rw [supportHomChangeTheta_apply, N.evaluation]
        have hr : rho ≫ d.inv ≫ f = rho₀ ≫ f := by
          rw [← hd, Category.assoc, Iso.hom_inv_id_assoc]
        rw [hr]
      chi := supportHomChangeChi J j B₀ B d N.chi
      naturality := by
        intro K M b a x
        rw [supportHomChangeChi_apply, supportHomChangeChi_apply, N.naturality]
        exact (Category.assoc _ _ _).symm
      cocycle := supportHomChangeCocycle J j B₀ B d N.theta N.chi N.cocycle }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def supportHomNormalizationChangeSupported
    {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (B : Sheaf S.topology (ModuleCat.{u + 1} A))
    (rho : (constantSheaf S.topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (d : S.supported ≅ B) (hd : S.constantRestriction ≫ d.hom = rho)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction B rho) :
    SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction :=
  supportHomNormalizationChangeSupportedGeneric S.topology S.isTerminal S.restriction
    S.supported S.constantRestriction B rho d hd N

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def supportHomEtaleTransport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) : etaleSupportHomTransport P i i' h := by
  letI : (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
      (etaleSupportHomPair P i).topology (etaleSupportHomPair P i').topology :=
    Etale.isContinuous_overPullback h
  letI : (MorphismProperty.Over.pullback @Etale ⊤ i).IsContinuous
      X.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback i
  letI : (MorphismProperty.Over.pullback @Etale ⊤ i').IsContinuous
      X'.smallEtaleTopology Z'.smallEtaleTopology := Etale.isContinuous_overPullback i'
  let t : (MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X)) ≅
      Scheme.Etale.mk (𝟙 X') :=
    MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
      (asIso (pullback.snd (𝟙 X) h)) (Category.comp_id _)
  have hn := SupportedConstantNormalization.scheme_normalization P false sq
  have : IsIso (SupportedConstantNormalization.exchange P.Coefficient false sq) :=
    hn.2.2.2.1
  refine {
    terminalMap := t.inv
    complementMap := supportHomEtaleComplementMap i i' h g sq
    restriction_square := ?_
    constantIso := (Scheme.upperStarConstantSheafIso
      (ModuleCat.{u + 1} P.Coefficient) h).app (ModuleCat.of P.Coefficient P.Coefficient)
    constantIso_spec := supportHomEtaleConstantIso_spec h
    closedIso := asIso (SupportedConstantNormalization.exchange P.Coefficient false sq)
    closedIso_spec := ?_
    supportUnit := SupportedConstantNormalization.sectionMap P false sq
    supportUnit_spec := ?_ }
  · as_aux_lemma =>
      exact ((MorphismProperty.Over.mkIdTerminal @Etale X').ofIso t.symm).hom_ext _ _
  · as_aux_lemma =>
      change (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).map
          (supportHomConstantDirectImage X.smallEtaleTopology Z.smallEtaleTopology
            (MorphismProperty.Over.pullback @Etale ⊤ i)) ≫
            SupportedConstantNormalization.exchange P.Coefficient false sq =
          ((Scheme.upperStarConstantSheafIso
            (ModuleCat.{u + 1} P.Coefficient) h).app
              (ModuleCat.of P.Coefficient P.Coefficient)).hom ≫
            supportHomConstantDirectImage X'.smallEtaleTopology Z'.smallEtaleTopology
              (MorphismProperty.Over.pullback @Etale ⊤ i')
      erw [← supportHomEtaleConstantIso_spec i, ← supportHomEtaleConstantIso_spec i']
      exact hn.2.2.2.2.1
  · exact (SupportedConstantNormalization.sectionMap_existsUnique P false sq).choose_spec.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def supportHomProEtaleTransport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) : proEtaleSupportHomTransport P i i' h := by
  letI := Scheme.ProEt.isContinuous_overPullback h
  let L := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h
  let t := ProEtale.overPullbackObjMkIdIso h
  have hn := SupportedConstantNormalization.scheme_normalization P true sq
  have : IsIso (SupportedConstantNormalization.exchange P.Coefficient true sq) :=
    hn.2.2.2.1
  refine {
    terminalMap := t.inv
    complementMap := supportHomProEtaleComplementMap i i' h g sq
    restriction_square := ?_
    constantIso := (ProEtale.constantSheafCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) h).app (ModuleCat.of P.Coefficient P.Coefficient)
    constantIso_spec := supportHomProEtaleConstantIso_spec h
    closedIso := L.mapIso (supportHomProEtaleSupportedIso P i) ≪≫
      asIso (SupportedConstantNormalization.exchange P.Coefficient true sq) ≪≫
        (supportHomProEtaleSupportedIso P i').symm
    closedIso_spec := ?_
    supportUnit := SupportedConstantNormalization.sectionMap P true sq
    supportUnit_spec := ?_ }
  · as_aux_lemma =>
      exact ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale X').ofIso t.symm).hom_ext _ _
  · as_aux_lemma =>
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
      rw [← L.map_comp_assoc, supportHomProEtaleSupportedIso_spec]
      erw [← Category.assoc, hn.2.2.2.2.1]
      have hr := supportHomProEtaleSupportedIso_spec P i'
      rw [← hr]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
  · exact (SupportedConstantNormalization.sectionMap_existsUnique P true sq).choose_spec.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def supportHomSiteTransport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    siteSupportHomTransport P i := by
  letI := Scheme.isContinuous_toProEt X
  letI : (MorphismProperty.Over.pullback @Etale ⊤ i).IsContinuous
      X.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback i
  letI : (MorphismProperty.Over.pullback @Etale ⊤ i).IsContinuous
      X.smallEtaleTopology (Scheme.smallGrothendieckTopology (@Etale) Z) :=
    Etale.isContinuous_overPullback i
  have hn := SupportedConstantNormalization.site_normalization P i
  have : IsIso (SupportedConstantNormalization.gamma P.Coefficient i) := hn.2.2.2.2.1
  refine {
    terminalMap := 𝟙 _
    complementMap := 𝟙 _
    restriction_square := ?_
    constantIso := ProEtale.comparisonUpperStarUnitIso P.Coefficient X
    constantIso_spec := supportHomComparisonConstantIso_spec X
    closedIso := asIso (SupportedConstantNormalization.gamma P.Coefficient i) ≪≫
      (supportHomProEtaleSupportedIso P i).symm
    closedIso_spec := ?_
    supportUnit := SupportedConstantNormalization.compareSectionMap P i
    supportUnit_spec := ?_ }
  · as_aux_lemma =>
      rfl
  · as_aux_lemma =>
      simp only [Iso.trans_hom, Iso.symm_hom]
      change (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
          (supportHomConstantDirectImage _ _ (MorphismProperty.Over.pullback @Etale ⊤ i)) ≫
        SupportedConstantNormalization.gamma P.Coefficient i ≫ _ = _
      erw [← supportHomEtaleConstantIso_spec i, ← Category.assoc, hn.2.2.2.2.2.1]
      rw [← supportHomProEtaleSupportedIso_spec P i]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · as_aux_lemma =>
      intro M
      have he := (SupportedConstantNormalization.compareSectionMap_existsUnique P i).choose_spec.1 M
      dsimp only [SupportedConstantNormalization.compareSigma] at he
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact he

private theorem supportHomEtaleTransport_closedIso_hom
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    ((supportHomEtaleTransport P i i' h g sq).closedIso
      (hB := Etale.isContinuous_overPullback h)).hom =
      SupportedConstantNormalization.exchange P.Coefficient false sq := by
  with_unfolding_all rfl

private theorem supportHomEtaleTransport_supportUnit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    (supportHomEtaleTransport P i i' h g sq).supportUnit
      (hB := Etale.isContinuous_overPullback h) =
      SupportedConstantNormalization.sectionMap P false sq := by
  with_unfolding_all rfl

private theorem supportHomProEtaleTransport_closedIso_hom
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    ((supportHomProEtaleTransport P i i' h g sq).closedIso
      (hB := Scheme.ProEt.isContinuous_overPullback h)).hom =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).map
        (supportHomProEtaleSupportedIso P i).hom ≫
          SupportedConstantNormalization.exchange P.Coefficient true sq ≫
            (supportHomProEtaleSupportedIso P i').inv := by
  with_unfolding_all rfl

private theorem supportHomProEtaleTransport_supportUnit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    (supportHomProEtaleTransport P i i' h g sq).supportUnit
      (hB := Scheme.ProEt.isContinuous_overPullback h) =
      SupportedConstantNormalization.sectionMap P true sq := by
  with_unfolding_all rfl

private theorem supportHomSiteTransport_closedIso_hom
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ((supportHomSiteTransport P i).closedIso
      (hB := Scheme.isContinuous_toProEt X)).hom =
      SupportedConstantNormalization.gamma P.Coefficient i ≫
        (supportHomProEtaleSupportedIso P i).inv := by
  with_unfolding_all rfl

private theorem supportHomSiteTransport_supportUnit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (supportHomSiteTransport P i).supportUnit
      (hB := Scheme.isContinuous_toProEt X) =
      SupportedConstantNormalization.compareSectionMap P i := by
  with_unfolding_all rfl

private theorem supportHomDerivedNatIso_refl
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryPlusNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategoryPlus := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  intro M
  rw [← cancel_mono (F.mapDerivedCategoryPlusFactorsh.hom.app M),
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def supportHomDerivedMapGeneric
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : C ⥤ E) (S' : D ⥤ E) [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso E)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := S) (G' := S') (β := L) (γ := 𝟭 E)
      ((Functor.rightUnitor _).hom ≫ tau)

private theorem supportHomDerivedSquareGeneric
    {C D C' D' E : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D'] [Category* E]
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D'] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [EnoughInjectives C'] [EnoughInjectives D']
    (G : C ⥤ E) (H : D ⥤ E) (G₀ : C' ⥤ E) (H₀ : D' ⥤ E)
    [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
    (N : C ⥤ D) (N' : C' ⥤ D') (LE : C ⥤ C') (LP : D ⥤ D')
    [N.Additive] [N'.Additive] [LE.Additive] [LP.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    [PreservesFiniteLimits LE] [PreservesFiniteColimits LE]
    [PreservesFiniteLimits LP] [PreservesFiniteColimits LP]
    (tv : G ⟶ N ⋙ H) (tv' : G₀ ⟶ N' ⋙ H₀)
    (te : G ⟶ LE ⋙ G₀) (tp : H ⟶ LP ⋙ H₀)
    (k : LE ⋙ N' ≅ N ⋙ LP)
    (hs : ∀ M, te.app M ≫ tv'.app (LE.obj M) ≫ H₀.map (k.hom.app M) =
      tv.app M ≫ tp.app (N.obj M))
    (K : DerivedCategory.Plus C) :
    (supportHomDerivedMapGeneric N G H tv).app K ≫
        (supportHomDerivedMapGeneric LP H H₀ tp).app (N.mapDerivedCategoryPlus.obj K) =
      (supportHomDerivedMapGeneric LE G G₀ te).app K ≫
        (supportHomDerivedMapGeneric N' G₀ H₀ tv').app (LE.mapDerivedCategoryPlus.obj K) ≫
          H₀.rightDerivedFunctorPlus.map
            (((Functor.mapDerivedCategoryPlusCompIso LE N').symm ≪≫
              Functor.mapDerivedCategoryPlusNatIso k ≪≫
                Functor.mapDerivedCategoryPlusCompIso N LP).hom.app K) := by
  let V := 𝟭 E
  have hc := Functor.rightDerivedFunctorPlusBaseChange_cube G H G₀ H₀
    N V N' V LE V LP V
    ((Functor.rightUnitor G).hom ≫ tv)
    ((Functor.rightUnitor G₀).hom ≫ tv')
    ((Functor.rightUnitor G).hom ≫ te)
    ((Functor.rightUnitor H).hom ≫ tp)
    (Iso.refl (V ⋙ V)) k (fun M => by
      simp only [V, NatTrans.comp_app, Functor.rightUnitor_hom_app, Functor.id_map,
        Iso.refl_inv, NatTrans.id_app, Category.id_comp]
      repeat erw [Category.id_comp]
      change tv.app M ≫
          tp.app (N.obj M) ≫
            H₀.map (k.inv.app M) =
        te.app M ≫
          tv'.app (LE.obj M)
      erw [← Category.assoc, ← hs M]
      simp only [Category.assoc]
      change _ ≫ _ ≫ H₀.map (k.hom.app M) ≫ H₀.map (k.inv.app M) = _
      erw [← H₀.map_comp, Iso.hom_inv_id_app, H₀.map_id, Category.comp_id]) K
  have hid : (Functor.mapDerivedCategoryPlusCompIso V V).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso (Iso.refl (V ⋙ V)) ≪≫
        Functor.mapDerivedCategoryPlusCompIso V V = Iso.refl _ := by
    rw [supportHomDerivedNatIso_refl]
    simp
  rw [hid] at hc
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hc
  let r := (Functor.mapDerivedCategoryPlusIdIso E).inv
  let bv := Functor.rightDerivedFunctorPlusBaseChange
    ((Functor.rightUnitor G).hom ≫ tv)
  let be := Functor.rightDerivedFunctorPlusBaseChange
    ((Functor.rightUnitor G).hom ≫
      te)
  have hv := r.naturality (bv.app K)
  have he := r.naturality (be.app K)
  simp only [Functor.id_map] at hv he
  apply (cancel_mono (H₀.rightDerivedFunctorPlus.map
    (((Functor.mapDerivedCategoryPlusCompIso LE N').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso k ≪≫
        Functor.mapDerivedCategoryPlusCompIso N LP).inv.app K))).mp
  simp only [supportHomDerivedMapGeneric, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc]
  erw [← H₀.rightDerivedFunctorPlus.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [reassoc_of% hv, reassoc_of% he]
  exact congrArg (fun f => r.app (G.rightDerivedFunctorPlus.obj K) ≫
    r.app (V.mapDerivedCategoryPlus.obj (G.rightDerivedFunctorPlus.obj K)) ≫ f) hc

private theorem supportHomDerivedSquare
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X)
    (e : etaleSupportHomTransport P i i' h) (p : proEtaleSupportHomTransport P i i' h)
    (v : siteSupportHomTransport P i) (v' : siteSupportHomTransport P i')
    (hs : ∀ M, (e.supportUnit (hB := Etale.isContinuous_overPullback h)).app M ≫
      (v'.supportUnit (hB := Scheme.isContinuous_toProEt X')).app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).obj M) ≫
      (proEtaleSupportHomPair P i').sections.map
        ((ProEtale.supportSiteComparisonCoefficientPullbackIso
          (ModuleCat.{u + 1} P.Coefficient) h).hom.app M) =
      (v.supportUnit (hB := Scheme.isContinuous_toProEt X)).app M ≫
        (p.supportUnit (hB := Scheme.ProEt.isContinuous_overPullback h)).app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M))
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (v.derivedMap (hB := Scheme.isContinuous_toProEt X)).app K ≫
      (p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback h)).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj K) =
      (e.derivedMap (hB := Etale.isContinuous_overPullback h)).app K ≫
        (v'.derivedMap (hB := Scheme.isContinuous_toProEt X')).app
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj K) ≫
        (proEtaleSupportHomPair P i').sections.rightDerivedFunctorPlus.map
          ((supportHomDerivedComparison P h).hom.app K) := by
  simpa only [supportHomDerivedMapGeneric, SupportHomPair.Transport.derivedMap,
    supportHomDerivedComparison] using
    supportHomDerivedSquareGeneric
      (etaleSupportHomPair P i).sections (proEtaleSupportHomPair P i).sections
      (etaleSupportHomPair P i').sections (proEtaleSupportHomPair P i').sections
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X')
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
      (v.supportUnit (hB := Scheme.isContinuous_toProEt X))
      (v'.supportUnit (hB := Scheme.isContinuous_toProEt X'))
      (e.supportUnit (hB := Etale.isContinuous_overPullback h))
      (p.supportUnit (hB := Scheme.ProEt.isContinuous_overPullback h))
      (ProEtale.supportSiteComparisonCoefficientPullbackIso
        (ModuleCat.{u + 1} P.Coefficient) h) hs K

private theorem supportHomCompatible
    {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
    {B : S.Site ⥤ T.Site} [B.IsContinuous S.topology T.topology]
    {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.topology (ModuleCat.{u + 1} A)}
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
    (e : SupportHomPair.Transport S T B L adj)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction)
    (N' : SupportedHomCocycleNormalization T.topology A T.isTerminal T.restriction
      T.supported T.constantRestriction)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :
    e.Compatible (supportHomIdentificationOfNormalization S N)
      (supportHomIdentificationOfNormalization T N') K a := by
  simp only [SupportHomPair.Transport.Compatible,
    supportHomIdentificationOfNormalization_chi]
  exact moduleSupportedHom_transport S.topology T.topology S.isTerminal S.restriction
    T.isTerminal T.restriction S.supported T.supported S.constantRestriction
    T.constantRestriction N N' L e.closedIso e.supportUnit (supportHomEvaluationSquare e N N')
    K a

private theorem supportHomNormalizedPairs
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Nonempty (SupportedHomCocycleNormalization (etaleSupportHomPair P i).topology
      P.Coefficient (etaleSupportHomPair P i).isTerminal
      (etaleSupportHomPair P i).restriction (etaleSupportHomPair P i).supported
      (etaleSupportHomPair P i).constantRestriction) ∧
    Nonempty (SupportedHomCocycleNormalization (proEtaleSupportHomPair P i).topology
      P.Coefficient (proEtaleSupportHomPair P i).isTerminal
      (proEtaleSupportHomPair P i).restriction (proEtaleSupportHomPair P i).supported
      (proEtaleSupportHomPair P i).constantRestriction) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ i).IsContinuous
      X.smallEtaleTopology (Scheme.smallGrothendieckTopology (@Etale) Z) :=
    Etale.isContinuous_overPullback i
  obtain ⟨N, ⟨N'⟩, _, _, _⟩ := supportedHom_cocycle_normalization P i
  constructor
  · refine ⟨supportHomNormalizationChangeSupported (etaleSupportHomPair P i) _ _
      (Iso.refl _) ?_ N⟩
    change supportHomConstantDirectImage _ _ _ ≫ 𝟙 _ =
      Etale.supportedHomConstantRestriction P.Coefficient i
    rw [Category.comp_id]
    exact (supportHomEtaleConstantIso_spec i).symm
  · exact ⟨supportHomNormalizationChangeSupported (proEtaleSupportHomPair P i) _ _
      (supportHomProEtaleSupportedIso P i) (supportHomProEtaleSupportedIso_spec P i) N'⟩

private theorem supportHomSquare
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    SupportHomSquareCoherent P i i' h (supportHomEtaleTransport P i i' h g sq)
      (supportHomProEtaleTransport P i i' h g sq)
      (supportHomSiteTransport P i) (supportHomSiteTransport P i') := by
  obtain ⟨hc, hs⟩ := SupportedConstantNormalization.comparison_square P sq
  constructor
  · apply supportHomDerivedSquare
    intro M
    simp only [supportHomEtaleTransport_supportUnit,
      supportHomProEtaleTransport_supportUnit, supportHomSiteTransport_supportUnit]
    exact hs M
  · let LP := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h
    simp only [supportHomEtaleTransport_closedIso_hom,
      supportHomProEtaleTransport_closedIso_hom, supportHomSiteTransport_closedIso_hom,
      Functor.map_comp, Category.assoc]
    rw [Iso.inv_hom_id_map_assoc (supportHomProEtaleSupportedIso P i) LP]
    have hh := congrArg (fun f => f ≫ (supportHomProEtaleSupportedIso P i').inv) hc
    simp only [Category.assoc] at hh
    exact hh

/-- The canonical supported-Hom identifications commute with arbitrary pullback of a
closed pair in the etale topology and, for etale-origin coefficients, in the pro-etale
 topology. They also commute with comparison on both schemes, and the comparison
squares for supported groups and closed constants commute. Each identification is
normalized on every supported cocycle; each transport is fixed by the inverse-image
unit and the epic constant restriction. Thus the existential data introduce the
canonical maps, rather than allowing any choice of maps or identifications.

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and Example 9.5,
pp. 66--67, Ext proof; blueprint affine-line orientation, etale-origin transport
(blueprint: lem-pur-supported-hom-pullback).

Proof:
1. Use the canonical constant-exchange normalization to construct the two pullback
   transports and the two site-comparison transports. Their closed exchanges are
   normalized by the inverse-image unit and the epic constant restriction.
2. Use supported-Hom cocycle normalization for both sites. Transport the pro-etale
   normalization along the canonical isomorphism from the ordinary pro-etale
   supported constant to the etale-origin supported constant. Evaluation at 1
   identifies the inverse-image unit with each specified supported-section map.
3. Apply the module-valued transport lemma. It resolves the inverse image of an
   injective complex, compares the derived unit on cocycles, and then uses
   naturality to pass to every bounded-below derived object. It does not require
   inverse image to preserve injectives.
4. The canonical constant-exchange square gives coherence for closed objects and
   supported sections. The right-derived base-change cube gives coherence for
   the normalized derived supported maps. -/
theorem supportedHom_pullback (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ∃ chiE : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        (etaleSupportHomPair P i).Identification,
    ∃ chiP : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        (proEtaleSupportHomPair P i).Identification,
    ∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
      (_sq : ChosenCartesianSquare g i' i h),
    ∃ e : etaleSupportHomTransport P i i' h,
    ∃ p : proEtaleSupportHomTransport P i i' h,
    ∃ v : siteSupportHomTransport P i,
    ∃ v' : siteSupportHomTransport P i',
      SupportHomSquareCoherent P i i' h e p v v' ∧
      ∀ (F : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ),
        e.Compatible (hB := Etale.isContinuous_overPullback h) (chiE i) (chiE i') F a ∧
        p.Compatible (hB := Scheme.ProEt.isContinuous_overPullback h) (chiP i) (chiP i')
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj F) a ∧
        v.Compatible (hB := Scheme.isContinuous_toProEt X) (chiE i) (chiP i) F a ∧
        v'.Compatible (hB := Scheme.isContinuous_toProEt X') (chiE i') (chiP i')
          ((Etale.upperStar
            (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj F) a := by
  classical
  let NE : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      SupportedHomCocycleNormalization (etaleSupportHomPair P i).topology
        P.Coefficient (etaleSupportHomPair P i).isTerminal
        (etaleSupportHomPair P i).restriction (etaleSupportHomPair P i).supported
        (etaleSupportHomPair P i).constantRestriction :=
    fun i ↦ Classical.choice (supportHomNormalizedPairs P i).1
  let NP : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      SupportedHomCocycleNormalization (proEtaleSupportHomPair P i).topology
        P.Coefficient (proEtaleSupportHomPair P i).isTerminal
        (proEtaleSupportHomPair P i).restriction (proEtaleSupportHomPair P i).supported
        (proEtaleSupportHomPair P i).constantRestriction :=
    fun i ↦ Classical.choice (supportHomNormalizedPairs P i).2
  refine ⟨fun i ↦ supportHomIdentificationOfNormalization _ (NE i),
    fun i ↦ supportHomIdentificationOfNormalization _ (NP i), ?_⟩
  intro Z X Z' X' i hi i' hi' h g sq
  refine ⟨supportHomEtaleTransport P i i' h g sq,
    supportHomProEtaleTransport P i i' h g sq,
    supportHomSiteTransport P i, supportHomSiteTransport P i',
    supportHomSquare P i i' h g sq, ?_⟩
  let : (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
      (etaleSupportHomPair P i).topology (etaleSupportHomPair P i').topology :=
    Etale.isContinuous_overPullback h
  intro F a
  exact ⟨supportHomCompatible _ (NE i) (NE i') F a,
    supportHomCompatible _ (NP i) (NP i') _ a,
    supportHomCompatible _ (NE i) (NP i) F a,
    supportHomCompatible _ (NE i') (NP i') _ a⟩

end AlgebraicGeometry
