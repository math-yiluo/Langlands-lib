/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorClassNaturality
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorForgetNormalization

/-!
# Relative torsor representatives and boundary signs

Source: Stacks Project, Tag 03AJ, and the relative refinement in blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, clause (a)
(blueprint: lem-pur-divisor-torsor-boundary-signs).

-- Q32 revalidation delivery of the reviewed statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.Etale

attribute [local irreducible] relativeFiberMap

/-- The constant section one of the extension presentation.
Source: Stacks Tag 03AJ (blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorExtensionOne (T : Scheme.{u}) (U : T.Etale) :
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.obj (op U) :=
  (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op U) ⟨1⟩

/-- First signed coordinate of the actual shifted cone, transported out of extension by zero.
Source: Stacks Tag 03AJ, signed relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorSignedA (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    (relativeSectionComplex T U I).X ((q : ℤ) + 1) ⟶
      (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((CochainComplex.mappingCone (relativeSectionRestriction T U I)).shiftFunctorObjXIso
    (-1) ((q : ℤ) + 1) q (add_neg_cancel_right (q : ℤ) 1).symm).hom ≫
  homotopyCofiber.fstX (relativeSectionRestriction T U I) q ((q : ℤ) + 1) rfl ≫
  ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat (Nat.cast_add q 1)).hom

/-- Second signed coordinate is minus the ordinary cone's second coordinate.
Thus the differential reads `(da,res a-db)`.
Source: Stacks Tag 03AJ, signed relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorSignedB (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    (relativeSectionComplex T U I).X ((q : ℤ) + 1) ⟶ (I.X q).obj.obj (op U) :=
  -(((CochainComplex.mappingCone (relativeSectionRestriction T U I)).shiftFunctorObjXIso
    (-1) ((q : ℤ) + 1) q (add_neg_cancel_right (q : ℤ) 1).symm).hom ≫
    homotopyCofiber.sndX (relativeSectionRestriction T U I) q ≫
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
        ComplexShape.embeddingUpNat rfl).hom)

/-- A signed pair represents a class precisely when it is the coordinates of a cycle
mapping to that class under Mathlib's homology quotient.
Source: Stacks Tag 03AJ, relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def TorsorSignedRepresents (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op U))
    (x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)) : Prop :=
  ∃ z : (relativeSectionComplex T U I).cycles ((q : ℤ) + 1),
    torsorSignedA T U I q ((relativeSectionComplex T U I).iCycles _ z) = a ∧
    torsorSignedB T U I q ((relativeSectionComplex T U I).iCycles _ z) = b ∧
    (relativeSectionComplex T U I).homologyπ _ z = x

/-- Localization boundary induced by the actual shifted cone inclusion. In signed
coordinates it sends `b` to `(0,-b)`.
Source: Stacks Tag 0G71; Tag 03AJ, relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorLocalizationBoundary (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℤ) :
    (relativeSections U I).homology q ⟶ (relativeSectionComplex T U I).homology (q + 1) :=
  (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q + 1) q
    ((congrArg (fun n : ℤ ↦ -1 + n) (add_comm q 1)).trans
      (neg_add_cancel_left 1 q))).inv.app (relativeSections U I) ≫
  homologyMap ((shiftFunctor _ (-1 : ℤ)).map
    (CochainComplex.mappingCone.inr (relativeSectionRestriction T U I))) (q + 1)

/-- The class of an ordinary section cocycle, using the extension-by-zero transport.
Source: Stacks Tags 011J and 03AJ
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def TorsorSectionRepresents {T : Scheme.{u}} (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op U)) (x : (relativeSections U I).homology (q : ℤ)) : Prop :=
  ∃ z : (relativeSections U I).cycles (q : ℤ),
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat rfl).hom ((relativeSections U I).iCycles q z) = b ∧
    (relativeSections U I).homologyπ q z = x

/-- The evaluated split resolution sequence over the specified open.
Source: Stacks Tags 011J and 013T
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorOpenShortComplex (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)) :=
  S.map (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})

/-- The representative and sign assertions for a simultaneous relative classification.
The extension presentation and resolution maps are arbitrary models, not chosen maps.
Source: Stacks Tag 03AJ and blueprint lem-pur-divisor-class.proof.md, clause (a)
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
structure DivisorTorsorBoundarySigns
    (e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1) : Prop where
  representative : ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (h : E.middle ⟶ I.cocomplex.X 0) (_hh : E.inclusion ≫ h = I.ι.f 0),
    ∃ a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cocomplex.X 1,
      E.projection ≫ a = h ≫ I.cocomplex.d 0 1 ∧
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 0
        (a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))))
        (h.hom.app (op (Scheme.Etale.mk W.ι))
          (E.generator (op (Scheme.Etale.mk W.ι)) P.2))
        (e T W G I (Quotient.mk _ P))
  resolutions : ∀ (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I J : InjectiveResolution G) (a : I.Hom J (𝟙 G))
    (P : Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι)),
    homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1 (e T W G I P) =
      e T W G J P
  localization : ∀ (T : Scheme.{u}) (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op (Scheme.Etale.mk W.ι)))
    (x : (relativeSections (Scheme.Etale.mk W.ι) I).homology q),
    TorsorSectionRepresents (Scheme.Etale.mk W.ι) I q b x →
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I q 0 (-b)
        (torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I q x)
  trivial : ∀ (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (g : G.obj.obj (op (Scheme.Etale.mk W.ι))),
    ∃ x : (relativeSections (Scheme.Etale.mk W.ι) I.cocomplex).homology 0,
      TorsorSectionRepresents (Scheme.Etale.mk W.ι) I.cocomplex 0
        ((I.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) x ∧
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 0 0
        ((I.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g)
        (e T W G I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩)) ∧
      e T W G I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩) =
        -(torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 0 x)
  coefficients : ∀ (T : Scheme.{u}) (W : T.Opens)
    (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (_hS : S.ShortExact) (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (K : InjectiveResolution S.X₃) (a : I.cocomplex ⟶ J.cocomplex)
    (b : J.cocomplex ⟶ K.cocomplex) (hab : a ≫ b = 0)
    (_ha : I.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (_hb : J.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ K.ι)
    (hs : ∀ n : ℕ, Nonempty (((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)),
    ∃ hOpen : (torsorOpenShortComplex T (Scheme.Etale.mk W.ι)
        (ShortComplex.mk a b hab)).ShortExact,
      ∀ (g : S.X₃.obj.obj (op (Scheme.Etale.mk W.ι))),
      ∃ x : (relativeSections (Scheme.Etale.mk W.ι) K.cocomplex).homology 0,
        TorsorSectionRepresents (Scheme.Etale.mk W.ι) K.cocomplex 0
          ((K.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) x ∧
        relativeConnecting T (Scheme.Etale.mk W.ι) (ShortComplex.mk a b hab) hs 1
            (e T W S.X₃ K (Quotient.mk _ ⟨Sheaf.Torsor.trivial S.X₃, g⟩)) =
          torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 1
            (hOpen.δ 0 1 rfl x) ∧
        ∀ (r : (J.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk W.ι)))
          (_hr : (b.f 0).hom.app (op (Scheme.Etale.mk W.ι)) r =
            (K.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g),
          ∃ c : (I.cocomplex.X 1).obj.obj (op (Scheme.Etale.mk W.ι)),
            (a.f 1).hom.app (op (Scheme.Etale.mk W.ι)) c =
              (J.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk W.ι)) r ∧
            TorsorSectionRepresents (Scheme.Etale.mk W.ι) I.cocomplex 1 c
              (hOpen.δ 0 1 rfl x) ∧
            TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 1 0 (-c)
              (relativeConnecting T (Scheme.Etale.mk W.ι) (ShortComplex.mk a b hab) hs 1
                (e T W S.X₃ K (Quotient.mk _ ⟨Sheaf.Torsor.trivial S.X₃, g⟩))) ∧
            TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 1 0 (-c)
              (torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 1
                (hOpen.δ 0 1 rfl x))
  extensions : ∀ (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (h h' : E.middle ⟶ I.cocomplex.X 0)
    (_hh : E.inclusion ≫ h = I.ι.f 0) (_hh' : E.inclusion ≫ h' = I.ι.f 0)
    (a a' : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cocomplex.X 1)
    (_ha : E.projection ≫ a = h ≫ I.cocomplex.d 0 1)
    (_ha' : E.projection ≫ a' = h' ≫ I.cocomplex.d 0 1),
    ∃ x : (I.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk (𝟙 T))),
      a'.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) -
        a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) =
        (I.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) x ∧
      h'.hom.app (op (Scheme.Etale.mk W.ι))
          (E.generator (op (Scheme.Etale.mk W.ι)) P.2) -
        h.hom.app (op (Scheme.Etale.mk W.ι))
          (E.generator (op (Scheme.Etale.mk W.ι)) P.2) =
        (I.cocomplex.X 0).obj.map
          ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op x
  coefficient_representatives : ∀ (T : Scheme.{u}) (W : T.Opens)
    (I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ J) (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op (Scheme.Etale.mk W.ι)))
    (x : (relativeSectionComplex T (Scheme.Etale.mk W.ι) I).homology ((q : ℤ) + 1)),
    TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I q a b x →
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) J q
        ((f.f (q + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) a)
        ((f.f q).hom.app (op (Scheme.Etale.mk W.ι)) b)
        (homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f) ((q : ℤ) + 1) x)
  restriction_representatives : ∀ (T T' : Scheme.{u}) (h : T' ⟶ T) [Etale h]
    (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J)
    (q : ℕ) (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op (Scheme.Etale.mk W.ι)))
    (x : (relativeSectionComplex T (Scheme.Etale.mk W.ι) I).homology ((q : ℤ) + 1)),
    TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I q a b x →
      TorsorSignedRepresents T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J q
        ((globalResolutionSectionTransfer h I J f).f (q + 1) a)
        ((openResolutionSectionTransfer h I J f W).f q b)
        (homologyMap (relativeTransfer h W I J f) ((q : ℤ) + 1) x)
  localization_coefficients : ∀ (T : Scheme.{u}) (W : T.Opens)
    (I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ J) (q : ℤ),
    torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I q ≫
        homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f) (q + 1) =
      homologyMap (extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat) q ≫
        torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) J q
  localization_restriction : ∀ (T T' : Scheme.{u}) (h : T' ⟶ T) [Etale h]
    (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J)
    (q : ℤ),
    torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I q ≫
        homologyMap (relativeTransfer h W I J f) (q + 1) =
      homologyMap (extendMap (openResolutionSectionTransfer h I J f W)
        ComplexShape.embeddingUpNat) q ≫
        torsorLocalizationBoundary T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J q
  connecting_coefficients : ∀ (T : Scheme.{u}) (W : T.Opens)
    (S S' : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (hs' : ∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (f : S ⟶ S') (q : ℤ),
    relativeConnecting T (Scheme.Etale.mk W.ι) S hs q ≫
        homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f.τ₁) (q + 1) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f.τ₃) q ≫
        relativeConnecting T (Scheme.Etale.mk W.ι) S' hs' q
  connecting_restriction : ∀ (T T' : Scheme.{u}) (h : T' ⟶ T) [Etale h]
    (W : T.Opens)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (S' : ShortComplex
      (CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (hs' : ∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (f : S ⟶ S'.map ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)))
    (q : ℤ),
    relativeConnecting T (Scheme.Etale.mk W.ι) S hs q ≫
        homologyMap (relativeTransfer h W S.X₁ S'.X₁ f.τ₁) (q + 1) =
      homologyMap (relativeTransfer h W S.X₃ S'.X₃ f.τ₃) q ≫
        relativeConnecting T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' hs' q

/-- Canonical Mathlib sheafification instances cached for the cone calculations.
These aliases use the existing instances, with local instance registration only.
Source: Mathlib sheafification and section functors
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
private local instance (priority := 3000) torsorBoundaryHasSheafify
    (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

private local instance (priority := 3000) torsorBoundaryWEqualsLocallyBijective
    (T : Scheme.{u}) :
    T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

private local instance (priority := 3000) torsorBoundarySectionPreservesZero
    (T : Scheme.{u}) (U : T.Etale) :
    (etaleSectionFunctor U).PreservesZeroMorphisms := inferInstance

private local instance (priority := 3000) torsorBoundaryComplexSectionsPreservesZero
    (T : Scheme.{u}) (U : T.Etale) :
    ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).PreservesZeroMorphisms :=
  inferInstance

private local instance torsorBoundaryIdentityForget :
    HasForget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} where
  forget₂ := 𝟭 _
  forget_comp := rfl

private local instance torsorBoundaryIdentityForgetAdditive :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).Additive

private local instance torsorBoundaryIdentityForgetHomology :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).PreservesHomology

attribute [local irreducible] torsorSignedA torsorSignedB relativeTorsorEquiv

set_option backward.isDefEq.respectTransparency false in
private lemma connecting_cycle
    (R : ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℤ)) (hR : R.ShortExact)
    (q : ℤ) (z : R.X₃.cycles q) (v₂ : R.X₂.X q)
    (hv₂ : R.g.f q v₂ = R.X₃.iCycles q z) (v₁ : R.X₁.X (q + 1))
    (hv₁ : R.f.f (q + 1) v₁ = R.X₂.d q (q + 1) v₂) :
    ∃ w : R.X₁.cycles (q + 1), R.X₁.iCycles (q + 1) w = v₁ ∧
      R.X₁.homologyπ (q + 1) w = hR.δ q (q + 1) rfl (R.X₃.homologyπ q z) := by
  let v₃ := R.X₃.iCycles q z
  have hv₃ : R.X₃.d q (q + 1) v₃ = 0 :=
    ConcreteCategory.congr_hom (R.X₃.iCycles_d q (q + 1)) z
  have hd := hR.δ_apply q (q + 1) rfl v₃ hv₃ v₂ hv₂ v₁ hv₁ (q + 2) (by simp [add_assoc])
  have heq : R.X₃.cyclesMk (i := q) v₃ (q + 1) (by simp) hv₃ = z := by
    apply (AddCommGrpCat.mono_iff_injective (R.X₃.iCycles q)).1 inferInstance
    exact HomologicalComplex.i_cyclesMk R.X₃ (i := q) v₃ (q + 1) (by simp) hv₃
  change hR.δ q (q + 1) rfl
    (R.X₃.homologyπ q (R.X₃.cyclesMk (i := q) v₃ (q + 1) (by simp) hv₃)) = _ at hd
  rw [heq] at hd
  refine ⟨_, ?_, hd.symm⟩
  exact HomologicalComplex.i_cyclesMk R.X₁ (i := q + 1) v₁ (q + 2)
    (by simp [add_assoc]) (hR.d_eq_zero_of_f_eq_d_apply q (q + 1) v₂ v₁ hv₁ (q + 2))

set_option backward.isDefEq.respectTransparency false in
private lemma signedA_eq (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    torsorSignedA T U I 0 = relativeFst T U I 0 := by
  unfold torsorSignedA relativeFst relativeDegreeIso
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_fst]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma signedB_eq (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    torsorSignedB T U I 0 = -relativeSnd T U I 0 := by
  unfold torsorSignedB relativeSnd relativeDegreeIso CochainComplex.mappingCone
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_snd]
  have hs (i j : ℤ) (h : i + 1 = j) :
      (homotopyCofiber.XIsoBiprod (relativeSectionRestriction T U I) i j h).hom ≫
          biprod.snd = homotopyCofiber.sndX (relativeSectionRestriction T U I) i := by
    subst j
    apply homotopyCofiber.ext_from_X _ (i + 1) i rfl <;> simp
  exact (congrArg (fun f ↦ -(f ≫
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 0 = 0)).hom))
    (hs 0 1 rfl)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma frame_represents (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (z : ResolutionFramedLift T U I) :
    TorsorSignedRepresents T U I.cocomplex 0
      ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1)
      z.2.1 (relativeFrameClass T U I z) := by
  have hi : (relativeSectionComplex T U I.cocomplex).iCycles 1
      (relativeFrameCycle T U I z) = relativeFrameElement T U I z := by
    unfold relativeFrameCycle
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
    exact ShortComplex.abCyclesIso_inv_apply_iCycles _ _
  have hc := CategoryTheory.Iso.inv_hom_id_apply (relativeDegreeIso T U I.cocomplex 0)
    ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1,
      -(show (I.cocomplex.X 0).obj.obj (op U) from z.2.1))
  refine ⟨relativeFrameCycle T U I z, ?_, ?_, rfl⟩
  · erw [signedA_eq, hi]
    exact congrArg Prod.fst hc
  · erw [signedB_eq, hi]
    change -(relativeSnd T U I.cocomplex 0 (relativeFrameElement T U I z)) = _
    rw [show relativeSnd T U I.cocomplex 0 (relativeFrameElement T U I z) = -z.2.1 from
      congrArg Prod.snd hc, neg_neg]

set_option backward.isDefEq.respectTransparency false in
private def integerSectionEquiv (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ F) ≃+ F.obj.obj
        (op (Scheme.Etale.mk (𝟙 T))) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

set_option backward.isDefEq.respectTransparency false in
private lemma integerSectionEquiv_eval (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ F) :
    integerSectionEquiv T F a = a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) := by
  change ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homEquiv _ F a) ⟨1⟩ = _
  rw [Adjunction.homEquiv_unit]
  simp only [constantSheafAdj, Adjunction.comp, torsorExtensionOne]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma one_natural (T : Scheme.{u}) {U V : T.Etaleᵒᵖ} (f : U ⟶ V) :
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.map f (torsorExtensionOne T U.unop) =
      torsorExtensionOne T V.unop := by
  have h := ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality f) ⟨1⟩
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
private lemma integerSectionEquiv_restrict (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ F) (U : T.Etaleᵒᵖ) :
    a.hom.app U (torsorExtensionOne T U.unop) =
      F.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
        (integerSectionEquiv T F a) := by
  rw [integerSectionEquiv_eval]
  have h := ConcreteCategory.congr_hom
    (a.hom.naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op)
        (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))
  simp only [ConcreteCategory.comp_apply] at h
  erw [one_natural] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private def extensionLiftMap (T : Scheme.{u})
    {G F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {P : Sheaf.Torsor G} (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P)
    (h : E.middle ⟶ F) : P.sheaf.obj ⟶ F.obj ⋙ forget AddCommGrpCat.{u + 1} where
  app A := TypeCat.ofHom fun t ↦ h.hom.app A (E.generator A t)
  naturality A B f := by
    ext t
    change h.hom.app B (E.generator B (P.sheaf.obj.map f t)) =
      F.obj.map f (h.hom.app A (E.generator A t))
    rw [← E.generator_natural]
    exact ConcreteCategory.congr_hom (h.hom.naturality f) (E.generator A t)

set_option backward.isDefEq.respectTransparency false in
private lemma extensionLiftMap_vadd (T : Scheme.{u})
    {G F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {P : Sheaf.Torsor G} (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P)
    (h : E.middle ⟶ F) (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.sheaf.obj.obj A) :
    (extensionLiftMap T E h).app A (P.vadd A g t) =
      (show F.obj.obj A from (extensionLiftMap T E h).app A t) +
        (E.inclusion ≫ h).hom.app A g := by
  change h.hom.app A (E.generator A (P.vadd A g t)) = _
  rw [E.generator_vadd, map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma extension_hom_ext (T : Scheme.{u})
    {G F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {P : Sheaf.Torsor G} (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P)
    (h h' : E.middle ⟶ F) (hi : E.inclusion ≫ h = E.inclusion ≫ h')
    (hg : ∀ A t, h.hom.app A (E.generator A t) = h'.hom.app A (E.generator A t)) :
    h = h' := by
  obtain ⟨l, hl, hu⟩ := E.universal F (E.inclusion ≫ h)
    (fun A t ↦ h.hom.app A (E.generator A t))
    (fun A B f t ↦ (ConcreteCategory.congr_hom
      ((extensionLiftMap T E h).naturality f) t).symm)
    (extensionLiftMap_vadd T E h)
  exact (hu h ⟨rfl, fun _ _ ↦ rfl⟩).trans
    (hu h' ⟨hi.symm, fun A t ↦ (hg A t).symm⟩).symm

set_option backward.isDefEq.respectTransparency false in
private lemma extension_d_generator (T : Scheme.{u})
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    {P : Sheaf.Torsor G} (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P)
    (h : E.middle ⟶ I.cocomplex.X 0)
    (a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cocomplex.X 1)
    (ha : E.projection ≫ a = h ≫ I.cocomplex.d 0 1)
    (A : T.Etaleᵒᵖ) (t : P.sheaf.obj.obj A) :
    (I.cocomplex.d 0 1).hom.app A ((extensionLiftMap T E h).app A t) =
      (I.cocomplex.X 1).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from A.unop).op
        (integerSectionEquiv T (I.cocomplex.X 1) a) := by
  have he := congrArg (fun k : E.middle ⟶ I.cocomplex.X 1 ↦
    k.hom.app A (E.generator A t)) ha
  change a.hom.app A (E.projection.hom.app A (E.generator A t)) = _ at he
  erw [E.projection_generator] at he
  change a.hom.app A (torsorExtensionOne T A.unop) = _ at he
  rw [integerSectionEquiv_restrict] at he
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
private lemma extension_representation (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G U)
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (h : E.middle ⟶ I.cocomplex.X 0) (hh : E.inclusion ≫ h = I.ι.f 0) :
    ∃ a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cocomplex.X 1,
      E.projection ≫ a = h ≫ I.cocomplex.d 0 1 ∧
      TorsorSignedRepresents T U I.cocomplex 0
        (a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))))
        (h.hom.app (op U) (E.generator (op U) P.2))
        (relativeTorsorEquiv T U I (Quotient.mk _ P)) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let μ := extensionLiftMap T E h
  let d := I.cocomplex.toCycles 0 1
  have hι : I.ι.f 0 ≫ d = 0 := (resolutionLiftSequence T I).zero
  obtain ⟨s, hs⟩ := Sheaf.Torsor.exists_section_of_invariant P.1
    ((sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj
      (I.cocomplex.cycles 1)) hT
    (fun A t ↦ d.hom.app A (μ.app A t))
    (fun A B f t ↦ by
      change (I.cocomplex.cycles 1).obj.map f (d.hom.app A (μ.app A t)) = _
      have hd := ConcreteCategory.congr_hom (d.hom.naturality f) (μ.app A t)
      change d.hom.app B ((I.cocomplex.X 0).obj.map f (μ.app A t)) = _ at hd
      simp only [ConcreteCategory.comp_apply] at hd
      erw [← hd]
      exact congrArg (d.hom.app B)
        (ConcreteCategory.congr_hom (μ.naturality f) t).symm)
    (fun A g t ↦ by
      change d.hom.app A ((extensionLiftMap T E h).app A (P.1.vadd A g t)) = _
      rw [extensionLiftMap_vadd, hh, map_add]
      have hz := congrArg (fun k : G ⟶ I.cocomplex.cycles 1 ↦ k.hom.app A g) hι
      change d.hom.app A ((I.ι.f 0).hom.app A g) = 0 at hz
      erw [hz, add_zero])
  change ∀ A t, d.hom.app A (μ.app A t) =
    (I.cocomplex.cycles 1).obj.map (hT.from A.unop).op s at hs
  let Q : Sheaf.Torsor G := Sheaf.Torsor.lifts (G := G) hT (resolutionLiftSequence_shortExact T I) s
  let f : P.1.sheaf ⟶ Q.sheaf := ⟨{
    app A := TypeCat.ofHom fun t ↦ ⟨μ.app A t, hs A t⟩
    naturality A B k := by
      ext t
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (μ.naturality k) t }⟩
  let ε : P.1.Iso Q := Sheaf.Torsor.Iso.ofHom f (fun A g t ↦ by
    apply Subtype.ext
    change (extensionLiftMap T E h).app A (P.1.vadd A g t) =
      (show (I.cocomplex.X 0).obj.obj A from μ.app A t) +
        (I.ι.f 0).hom.app A g
    rw [extensionLiftMap_vadd, hh]
    rfl)
  let a := (integerSectionEquiv T (I.cocomplex.X 1)).symm
    ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s)
  have ha_eval : a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) =
        (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s := by
    rw [← integerSectionEquiv_eval]
    exact (integerSectionEquiv T (I.cocomplex.X 1)).apply_symm_apply _
  refine ⟨a, ?_, ?_⟩
  · apply extension_hom_ext T E
    · rw [← Category.assoc, E.inclusion_projection, zero_comp, ← Category.assoc, hh,
        I.ι_f_zero_comp_complex_d]
    · intro A t
      change a.hom.app A (E.projection.hom.app A (E.generator A t)) =
        (I.cocomplex.d 0 1).hom.app A (μ.app A t)
      erw [E.projection_generator]
      change a.hom.app A (torsorExtensionOne T A.unop) = _
      rw [integerSectionEquiv_restrict]
      change (I.cocomplex.X 1).obj.map (hT.from A.unop).op
        (integerSectionEquiv T (I.cocomplex.X 1) a) = _
      rw [show integerSectionEquiv T (I.cocomplex.X 1) a =
        (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s from
          (integerSectionEquiv T (I.cocomplex.X 1)).apply_symm_apply _]
      have hn := ConcreteCategory.congr_hom
        ((I.cocomplex.iCycles 1).hom.naturality (hT.from A.unop).op) s
      change (I.cocomplex.iCycles 1).hom.app A
        ((I.cocomplex.cycles 1).obj.map (hT.from A.unop).op s) = _ at hn
      simp only [ConcreteCategory.comp_apply] at hn
      erw [← hn, ← hs A t]
      exact congrArg (fun k ↦ k.hom.app A (μ.app A t))
        (I.cocomplex.toCycles_i 0 1)
  · rw [ha_eval, relativeTorsorEquiv_presentation T U I P s ε]
    exact frame_represents T U I ⟨s, ε.iso.hom.hom.app (op U) P.2⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma coneMap_fst
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (n : ℤ) :
    (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f n ≫
        homotopyCofiber.fstX r' n (n + 1) rfl =
      homotopyCofiber.fstX r n (n + 1) rfl ≫ a.f (n + 1) := by
  dsimp only [homotopyCofiber.fstX]
  rw [← Category.assoc, coneMap_XIso]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma cone_snd {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (i : ℤ) :
    (homotopyCofiber.XIsoBiprod r i (i + 1) rfl).hom ≫ biprod.snd =
      homotopyCofiber.sndX r i := by
  apply homotopyCofiber.ext_from_X r (i + 1) i rfl <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma coneMap_snd
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (n : ℤ) :
    (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f n ≫
        homotopyCofiber.sndX r' n = homotopyCofiber.sndX r n ≫ b.f n := by
  rw [← cone_snd r' n, ← cone_snd r n, ← Category.assoc, coneMap_XIso]
  simp

section LinearConeCoordinates

variable {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℕ}

private def linearConeFirst
    (r : A.extend ComplexShape.embeddingUpNat ⟶ B.extend ComplexShape.embeddingUpNat)
    (q : ℕ) : ((CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧).X ((q : ℤ) + 1) ⟶
      A.X (q + 1) :=
  ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) ((q : ℤ) + 1) q
    (add_neg_cancel_right (q : ℤ) 1).symm).hom ≫
    homotopyCofiber.fstX r q ((q : ℤ) + 1) rfl ≫
    (A.extendXIso ComplexShape.embeddingUpNat (Nat.cast_add q 1)).hom

private def linearConeSecond
    (r : A.extend ComplexShape.embeddingUpNat ⟶ B.extend ComplexShape.embeddingUpNat)
    (q : ℕ) : ((CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧).X ((q : ℤ) + 1) ⟶ B.X q :=
  -(((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) ((q : ℤ) + 1) q
    (add_neg_cancel_right (q : ℤ) 1).symm).hom ≫ homotopyCofiber.sndX r q ≫
      (B.extendXIso ComplexShape.embeddingUpNat rfl).hom)

variable
    (r : A.extend ComplexShape.embeddingUpNat ⟶ B.extend ComplexShape.embeddingUpNat)
    (r' : A'.extend ComplexShape.embeddingUpNat ⟶ B'.extend ComplexShape.embeddingUpNat)
    (α : A ⟶ A') (β : B ⟶ B')
    (h : extendMap α ComplexShape.embeddingUpNat ≫ r' =
      r ≫ extendMap β ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency false in
private lemma linearConeFirst_map (q : ℕ) :
    (relativeFiberMap r r' (extendMap α ComplexShape.embeddingUpNat)
      (extendMap β ComplexShape.embeddingUpNat) h).f ((q : ℤ) + 1) ≫
        linearConeFirst r' q = linearConeFirst r q ≫ α.f (q + 1) := by
  unfold linearConeFirst relativeFiberMap
  simp only [CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
  erw [XIsoOfEq_hom_naturality_assoc
    (homotopyCofiber.mapArrowHom _ _ (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk (extendMap α ComplexShape.embeddingUpNat)
        (extendMap β ComplexShape.embeddingUpNat) h))
    (show (q : ℤ) + 1 + -1 = q by omega)]
  erw [coneMap_fst_assoc]
  erw [extendMap_f _ _ (Nat.cast_add q 1)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma linearConeSecond_map (q : ℕ) :
    (relativeFiberMap r r' (extendMap α ComplexShape.embeddingUpNat)
      (extendMap β ComplexShape.embeddingUpNat) h).f ((q : ℤ) + 1) ≫
        linearConeSecond r' q = linearConeSecond r q ≫ β.f q := by
  unfold linearConeSecond relativeFiberMap
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]
  congr 1
  simp only [CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
  erw [XIsoOfEq_hom_naturality_assoc
    (homotopyCofiber.mapArrowHom _ _ (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk (extendMap α ComplexShape.embeddingUpNat)
        (extendMap β ComplexShape.embeddingUpNat) h))
    (show (q : ℤ) + 1 + -1 = q by omega)]
  erw [coneMap_snd_assoc]
  erw [extendMap_f _ _ (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma linearConeFirst_inr (q : ℕ) :
    ((shiftFunctor _ (-1 : ℤ)).map (CochainComplex.mappingCone.inr r)).f ((q : ℤ) + 1) ≫
      linearConeFirst r q = 0 := by
  unfold linearConeFirst
  simp only [CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
  erw [XIsoOfEq_hom_naturality_assoc (CochainComplex.mappingCone.inr r)
    (show (q : ℤ) + 1 + -1 = q by omega)]
  simp only [CochainComplex.mappingCone.inr, homotopyCofiber.inr_f]
  erw [homotopyCofiber.inrX_fstX_assoc, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private lemma linearConeSecond_inr (q : ℕ) :
    ((shiftFunctor _ (-1 : ℤ)).map (CochainComplex.mappingCone.inr r)).f ((q : ℤ) + 1) ≫
      linearConeSecond r q =
        -((CochainComplex.shiftFunctorObjXIso (B.extend ComplexShape.embeddingUpNat)
          (-1) ((q : ℤ) + 1) q (by omega)).hom ≫
          (B.extendXIso ComplexShape.embeddingUpNat rfl).hom) := by
  unfold linearConeSecond
  rw [Preadditive.comp_neg]
  congr 1
  simp only [CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
  erw [XIsoOfEq_hom_naturality_assoc (CochainComplex.mappingCone.inr r)
    (show (q : ℤ) + 1 + -1 = q by omega)]
  simp only [CochainComplex.mappingCone.inr, homotopyCofiber.inr_f]
  erw [homotopyCofiber.inrX_sndX_assoc]

end LinearConeCoordinates

set_option backward.isDefEq.respectTransparency false in
private lemma cone_inr_natural
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    CochainComplex.mappingCone.inr r ≫ homotopyCofiber.mapArrowHom r r'
        (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      b ≫ CochainComplex.mappingCone.inr r' := by
  simp [CochainComplex.mappingCone.inr, homotopyCofiber.mapArrowHom]

private def coneLocalization {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (q : ℤ) : B.homology q ⟶
      ((CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧).homology (q + 1) :=
  (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q + 1) q
    (by omega)).inv.app B ≫
      homologyMap ((shiftFunctor _ (-1 : ℤ)).map (CochainComplex.mappingCone.inr r)) (q + 1)

set_option backward.isDefEq.respectTransparency false in
private lemma coneLocalization_natural
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (q : ℤ) :
    coneLocalization r q ≫ homologyMap (relativeFiberMap r r' a b h) (q + 1) =
      homologyMap b q ≫ coneLocalization r' q := by
  unfold coneLocalization relativeFiberMap
  rw [Category.assoc, ← homologyMap_comp, ← Functor.map_comp, cone_inr_natural,
    Functor.map_comp, homologyMap_comp, ← Category.assoc]
  exact congrArg (· ≫ homologyMap ((shiftFunctor _ (-1 : ℤ)).map
    (CochainComplex.mappingCone.inr r')) (q + 1))
    ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q + 1) q
      (by omega)).inv.naturality b).symm

set_option backward.isDefEq.respectTransparency false in
private def shiftedCycle (B : CochainComplex AddCommGrpCat.{u + 1} ℤ) (q : ℤ)
    (z : B.cycles q) : (B⟦(-1 : ℤ)⟧).cycles (q + 1) :=
  ShortComplex.cyclesMap ((CochainComplex.shiftShortComplexFunctorIso
    AddCommGrpCat.{u + 1} (-1) (q + 1) q (by omega)).inv.app B) z

set_option backward.isDefEq.respectTransparency false in
private lemma shiftedCycle_i (B : CochainComplex AddCommGrpCat.{u + 1} ℤ) (q : ℤ)
    (z : B.cycles q) :
    (B⟦(-1 : ℤ)⟧).iCycles (q + 1) (shiftedCycle B q z) =
      (B.shiftFunctorObjXIso (-1) (q + 1) q (by omega)).inv (B.iCycles q z) := by
  unfold shiftedCycle
  erw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma shiftedCycle_pi (B : CochainComplex AddCommGrpCat.{u + 1} ℤ) (q : ℤ)
    (z : B.cycles q) :
    (B⟦(-1 : ℤ)⟧).homologyπ (q + 1) (shiftedCycle B q z) =
      (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q + 1) q
        (by omega)).inv.app B (B.homologyπ q z) := by
  rw [CochainComplex.ShiftSequence.shiftIso_inv_app]
  exact (ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality
    ((CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{u + 1}
      (-1) (q + 1) q (by omega)).inv.app B)) z).symm

set_option backward.isDefEq.respectTransparency false in
private lemma localization_represents (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op U)) (x : (relativeSections U I).homology q)
    (hx : TorsorSectionRepresents U I q b x) :
    TorsorSignedRepresents T U I q 0 (-b) (torsorLocalizationBoundary T U I q x) := by
  obtain ⟨z, hb, rfl⟩ := hx
  let B := relativeSections U I
  let r := relativeSectionRestriction T U I
  let f := (shiftFunctor _ (-1 : ℤ)).map (CochainComplex.mappingCone.inr r)
  let s := shiftedCycle B q z
  have hA : f.f ((q : ℤ) + 1) ≫ torsorSignedA T U I q = 0 := by
    unfold torsorSignedA
    exact linearConeFirst_inr
      (A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
        (.up ℕ)).obj I)
      (B := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I) r q
  have hB : f.f ((q : ℤ) + 1) ≫ torsorSignedB T U I q =
      -((B.shiftFunctorObjXIso (-1) ((q : ℤ) + 1) q (by omega)).hom ≫
        ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
          ComplexShape.embeddingUpNat rfl).hom) := by
    unfold torsorSignedB
    exact linearConeSecond_inr
      (A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
        (.up ℕ)).obj I)
      (B := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I) r q
  have hi : (relativeSectionComplex T U I).iCycles _ (cyclesMap f _ s) =
      f.f _ ((B⟦(-1 : ℤ)⟧).iCycles _ s) :=
    ConcreteCategory.congr_hom (cyclesMap_i f _) s
  refine ⟨cyclesMap f _ s, ?_, ?_, ?_⟩
  · rw [hi]
    erw [← ConcreteCategory.comp_apply (f.f _) (torsorSignedA T U I q), hA]
    rfl
  · rw [hi]
    erw [← ConcreteCategory.comp_apply (f.f _) (torsorSignedB T U I q), hB]
    change -(((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat rfl).hom
      ((B.shiftFunctorObjXIso (-1) ((q : ℤ) + 1) q (by omega)).hom
      ((B⟦(-1 : ℤ)⟧).iCycles _ (shiftedCycle B q z)))) = -b
    rw [shiftedCycle_i, Iso.inv_hom_id_apply]
    exact congrArg Neg.neg hb
  · have hp := (ConcreteCategory.congr_hom (homologyπ_naturality f _) s).symm
    change _ = homologyMap f _ ((B⟦(-1 : ℤ)⟧).homologyπ _ s) at hp
    rw [shiftedCycle_pi] at hp
    exact hp

set_option backward.isDefEq.respectTransparency false in
private lemma signedRep_neg (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op U))
    (x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1))
    (hx : TorsorSignedRepresents T U I q a b x) :
    TorsorSignedRepresents T U I q (-a) (-b) (-x) := by
  obtain ⟨z, ha, hb, hc⟩ := hx
  exact ⟨-z, by simp only [map_neg, ha], by simp only [map_neg, hb],
    by simp only [map_neg, hc]⟩

set_option backward.isDefEq.respectTransparency false in
private lemma signedRep_unique (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : (I.X 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X 0).obj.obj (op U))
    (x y : (relativeSectionComplex T U I).homology 1)
    (hx : TorsorSignedRepresents T U I 0 a b x)
    (hy : TorsorSignedRepresents T U I 0 a b y) : x = y := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  obtain ⟨z', ha', hb', rfl⟩ := hy
  congr 1
  apply (AddCommGrpCat.mono_iff_injective
    ((relativeSectionComplex T U I).iCycles 1)).1 inferInstance
  apply (ConcreteCategory.bijective_of_isIso (relativeDegreeIso T U I 0).hom).1
  apply Prod.ext
  · change relativeFst T U I 0 _ = relativeFst T U I 0 _
    erw [← signedA_eq, ha, ha']
  · change relativeSnd T U I 0 _ = relativeSnd T U I 0 _
    apply neg_injective
    change (-relativeSnd T U I 0) _ = (-relativeSnd T U I 0) _
    erw [← signedB_eq, hb, hb']

set_option backward.isDefEq.respectTransparency false in
private lemma sectionClass_of_closed (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op U))
    (hb : (I.d q (q + 1)).hom.app (op U) b = 0) :
    ∃ x : (relativeSections U I).homology q, TorsorSectionRepresents U I q b x := by
  let A := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I
  let e := A.extendXIso ComplexShape.embeddingUpNat (rfl :
    ComplexShape.embeddingUpNat.f q = (q : ℤ))
  have hd : (relativeSections U I).d (q : ℤ) ((q + 1 : ℕ) : ℤ) (e.inv b) = 0 := by
    erw [extend_d_eq A ComplexShape.embeddingUpNat rfl rfl]
    change (A.extendXIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f (q + 1) = ((q + 1 : ℕ) : ℤ))).inv
        ((I.d q (q + 1)).hom.app (op U) (e.hom (e.inv b))) = 0
    rw [Iso.inv_hom_id_apply, hb, map_zero]
  let z := HomologicalComplex.cyclesMk.{u + 1, u + 2}
    (relativeSections U I) (i := (q : ℤ)) (e.inv b) ((q + 1 : ℕ) : ℤ)
    (by simp) hd
  refine ⟨(relativeSections U I).homologyπ q z, z, ?_, rfl⟩
  change e.hom ((relativeSections U I).iCycles q z) = b
  have hi := HomologicalComplex.i_cyclesMk.{u + 1, u + 2}
    (relativeSections U I) (i := (q : ℤ)) (e.inv b) ((q + 1 : ℕ) : ℤ) (by simp) hd
  exact (congrArg (fun t ↦ e.hom t) hi).trans (Iso.inv_hom_id_apply e b)

set_option backward.isDefEq.respectTransparency false in
private lemma trivial_represents (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (g : G.obj.obj (op U)) :
    TorsorSignedRepresents T U I.cocomplex 0 0 ((I.ι.f 0).hom.app (op U) g)
      (relativeTorsorEquiv T U I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩)) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  obtain ⟨ε, hε⟩ := Sheaf.Torsor.FramedLift.zero_isIsomorphic hT
    (G := G) (ι := I.ι.f 0) (d := I.cocomplex.toCycles 0 1)
    (resolutionLiftSequence_shortExact T I) U
  let ε' : (Sheaf.Torsor.trivial G).Iso
      (Sheaf.Torsor.lifts (G := G) hT (resolutionLiftSequence_shortExact T I) 0) := ε
  let z : ResolutionFramedLift T U I := ⟨0, ε'.iso.hom.hom.app (op U) g⟩
  have hb : (show (I.cocomplex.X 0).obj.obj (op U) from z.2.1) =
      (I.ι.f 0).hom.app (op U) g := by
    have h := congrArg Subtype.val (ε'.map_vadd (op U) g
      (show G.obj.obj (op U) from 0))
    have h0 := congrArg Subtype.val hε
    change (ε'.iso.hom.hom.app (op U) (g + 0)).1 =
      (show (I.cocomplex.X 0).obj.obj (op U) from
        (ε'.iso.hom.hom.app (op U) (show G.obj.obj (op U) from 0)).1) +
        (I.ι.f 0).hom.app (op U) g at h
    change (ε'.iso.hom.hom.app (op U) (show G.obj.obj (op U) from 0)).1 = 0 at h0
    simpa only [add_zero, h0, zero_add] using h
  rw [relativeTorsorEquiv_presentation T U I ⟨Sheaf.Torsor.trivial G, g⟩ 0 ε]
  have ht := frame_represents T U I z
  change TorsorSignedRepresents T U I.cocomplex 0
    ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1)
    (show (I.cocomplex.X 0).obj.obj (op U) from z.2.1)
    (relativeFrameClass T U I z) at ht
  erw [hb] at ht
  simpa only [z, map_zero] using ht

set_option backward.isDefEq.respectTransparency false in
private lemma trivial_boundary (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (g : G.obj.obj (op U)) :
    ∃ x : (relativeSections U I.cocomplex).homology 0,
      TorsorSectionRepresents U I.cocomplex 0 ((I.ι.f 0).hom.app (op U) g) x ∧
      TorsorSignedRepresents T U I.cocomplex 0 0 ((I.ι.f 0).hom.app (op U) g)
        (relativeTorsorEquiv T U I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩)) ∧
      relativeTorsorEquiv T U I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩) =
        -(torsorLocalizationBoundary T U I.cocomplex 0 x) := by
  have hg : (I.cocomplex.d 0 1).hom.app (op U) ((I.ι.f 0).hom.app (op U) g) = 0 :=
    congrArg (fun k : G ⟶ I.cocomplex.X 1 ↦ k.hom.app (op U) g)
      I.ι_f_zero_comp_complex_d
  obtain ⟨x, hx⟩ := sectionClass_of_closed T U I.cocomplex 0 _ hg
  have he := trivial_represents T U I g
  refine ⟨x, hx, he, signedRep_unique T U I.cocomplex 0 _ _ _ he ?_⟩
  simpa only [neg_zero, neg_neg] using signedRep_neg T U I.cocomplex 0 0
    (-((I.ι.f 0).hom.app (op U) g)) (torsorLocalizationBoundary T U I.cocomplex 0 x)
    (localization_represents T U I.cocomplex 0 _ x hx)

section RepresentativeMaps

variable (T T' : Scheme.{u}) (U : T.Etale) (U' : T'.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (α : ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj I ⟶
      ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex (.up ℕ)).obj J)
    (β : ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I ⟶
      ((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj J)
    (h : extendMap α ComplexShape.embeddingUpNat ≫ relativeSectionRestriction T' U' J =
      relativeSectionRestriction T U I ≫ extendMap β ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency false in
private lemma signedMap_A (q : ℕ) :
    (relativeFiberMap _ _ (extendMap α ComplexShape.embeddingUpNat)
      (extendMap β ComplexShape.embeddingUpNat) h).f ((q : ℤ) + 1) ≫
        torsorSignedA T' U' J q = torsorSignedA T U I q ≫ α.f (q + 1) := by
  unfold torsorSignedA
  exact linearConeFirst_map
    (A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
      (.up ℕ)).obj I)
    (B := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I)
    (A' := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex
      (.up ℕ)).obj J)
    (B' := ((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj J)
    (relativeSectionRestriction T U I) (relativeSectionRestriction T' U' J) α β h q

set_option backward.isDefEq.respectTransparency false in
private lemma signedMap_B (q : ℕ) :
    (relativeFiberMap _ _ (extendMap α ComplexShape.embeddingUpNat)
      (extendMap β ComplexShape.embeddingUpNat) h).f ((q : ℤ) + 1) ≫
        torsorSignedB T' U' J q = torsorSignedB T U I q ≫ β.f q := by
  unfold torsorSignedB
  exact linearConeSecond_map
    (A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
      (.up ℕ)).obj I)
    (B := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I)
    (A' := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex
      (.up ℕ)).obj J)
    (B' := ((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj J)
    (relativeSectionRestriction T U I) (relativeSectionRestriction T' U' J) α β h q

set_option backward.isDefEq.respectTransparency false in
private lemma signedRep_map (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op U))
    (x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1))
    (hx : TorsorSignedRepresents T U I q a b x) :
    TorsorSignedRepresents T' U' J q (α.f (q + 1) a) (β.f q b)
      (homologyMap (relativeFiberMap _ _ (extendMap α ComplexShape.embeddingUpNat)
        (extendMap β ComplexShape.embeddingUpNat) h) ((q : ℤ) + 1) x) := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  let f := relativeFiberMap _ _ (extendMap α ComplexShape.embeddingUpNat)
    (extendMap β ComplexShape.embeddingUpNat) h
  have hi : (relativeSectionComplex T' U' J).iCycles _ (cyclesMap f _ z) =
      f.f _ ((relativeSectionComplex T U I).iCycles _ z) := by
    exact ConcreteCategory.congr_hom (cyclesMap_i f _) z
  refine ⟨cyclesMap f _ z, ?_, ?_, ?_⟩
  · rw [hi]
    erw [← ConcreteCategory.comp_apply (f.f _) (torsorSignedA T' U' J q),
      signedMap_A T T' U U' I J α β h, ConcreteCategory.comp_apply, ha]
    rfl
  · rw [hi]
    erw [← ConcreteCategory.comp_apply (f.f _) (torsorSignedB T' U' J q),
      signedMap_B T T' U U' I J α β h, ConcreteCategory.comp_apply, hb]
    rfl
  · exact (ConcreteCategory.congr_hom (homologyπ_naturality f _) z).symm

end RepresentativeMaps

set_option backward.isDefEq.respectTransparency false in
private lemma signedA_one (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    torsorSignedA T U I 1 = relativeFst T U I 1 := by
  unfold torsorSignedA relativeFst relativeDegreeIso
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_fst]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma signedB_one (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    torsorSignedB T U I 1 = -relativeSnd T U I 1 := by
  unfold torsorSignedB relativeSnd relativeDegreeIso CochainComplex.mappingCone
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_snd]
  have hs (i j : ℤ) (h : i + 1 = j) :
      (homotopyCofiber.XIsoBiprod (relativeSectionRestriction T U I) i j h).hom ≫
          biprod.snd = homotopyCofiber.sndX (relativeSectionRestriction T U I) i := by
    subst j
    apply homotopyCofiber.ext_from_X _ (i + 1) i rfl <;> simp
  exact (congrArg (fun f ↦ -(f ≫
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 1 = 1)).hom))
    (hs 1 2 rfl)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma extendedSections_split (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (q : ℤ) : Nonempty ((S.map
      ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ) ⋙
        ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
          (HomologicalComplex.eval _ (.up ℤ) q)).Splitting := by
  classical
  let F := etaleSectionFunctor U
  let E := ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  let R := S.map (F.mapHomologicalComplex (.up ℕ) ⋙ E)
  change Nonempty (R.map (HomologicalComplex.eval _ (.up ℤ) q)).Splitting
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    let e : R.map (HomologicalComplex.eval _ (.up ℤ) (n : ℤ)) ≅
        (S.map (HomologicalComplex.eval _ (.up ℕ) n)).map F :=
      ShortComplex.isoMk
        (HomologicalComplex.extendXIso _ _ rfl)
        (HomologicalComplex.extendXIso _ _ rfl)
        (HomologicalComplex.extendXIso _ _ rfl)
        (by
          change _ ≫ F.map (S.f.f n) =
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map S.f)
              ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _
          erw [HomologicalComplex.extendMap_f _ _ (rfl :
            ComplexShape.embeddingUpNat.f n = (n : ℤ))]
          simp)
        (by
          change _ ≫ F.map (S.g.f n) =
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map S.g)
              ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _
          erw [HomologicalComplex.extendMap_f _ _ (rfl :
            ComplexShape.embeddingUpNat.f n = (n : ℤ))]
          simp)
    exact ⟨((hs n).some.map F).ofIso e.symm⟩
  · have hz (I : CochainComplex
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
        IsZero ((E.obj ((F.mapHomologicalComplex (.up ℕ)).obj I)).X q) :=
      HomologicalComplex.isZero_extend_X _ _ _ (by simpa using hq)
    exact ⟨{
      r := 0
      s := 0
      f_r := (hz S.X₁).eq_of_src _ _
      s_g := (hz S.X₃).eq_of_src _ _
      id := (hz S.X₂).eq_of_src _ _ }⟩

set_option backward.isDefEq.respectTransparency false in
private lemma openShortExact (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)) :
    (torsorOpenShortComplex T U S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  exact (extendedSections_split T U S hs q).some.shortExact

private def sectionDegreeIso (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    (relativeSections U I).X (q : ℤ) ≅ (I.X q).obj.obj (op U) :=
  HomologicalComplex.extendXIso _ _ rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma sectionMap_degree (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) (q : ℕ) :
    (extendMap (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map f)
      ComplexShape.embeddingUpNat).f (q : ℤ) ≫ (sectionDegreeIso T U J q).hom =
      (sectionDegreeIso T U I q).hom ≫ (f.f q).hom.app (op U) := by
  erw [extendMap_f _ _ (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))]
  simp only [sectionDegreeIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma section_d_degree (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q n : ℕ) :
    (relativeSections U I).d (q : ℤ) (n : ℤ) ≫ (sectionDegreeIso T U I n).hom =
      (sectionDegreeIso T U I q).hom ≫ (I.d q n).hom.app (op U) := by
  erw [extend_d_eq _ ComplexShape.embeddingUpNat rfl rfl]
  simp only [sectionDegreeIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma openConnecting_represents (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hS : (torsorOpenShortComplex T U S).ShortExact)
    (g : (S.X₃.X 0).obj.obj (op U))
    (x : (relativeSections U S.X₃).homology 0)
    (hx : TorsorSectionRepresents U S.X₃ 0 g x)
    (r : (S.X₂.X 0).obj.obj (op U))
    (hr : (S.g.f 0).hom.app (op U) r = g)
    (c : (S.X₁.X 1).obj.obj (op U))
    (hc : (S.f.f 1).hom.app (op U) c = (S.X₂.d 0 1).hom.app (op U) r) :
    TorsorSectionRepresents U S.X₁ 1 c (hS.δ 0 1 rfl x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  let R := torsorOpenShortComplex T U S
  let v₃ := R.X₃.iCycles 0 z
  let v₂ := (sectionDegreeIso T U S.X₂ 0).inv r
  let v₁ := (sectionDegreeIso T U S.X₁ 1).inv c
  have hv₂ : R.g.f 0 v₂ = v₃ := by
    apply (ConcreteCategory.bijective_of_isIso (sectionDegreeIso T U S.X₃ 0).hom).1
    calc
      _ = (S.g.f 0).hom.app (op U) ((sectionDegreeIso T U S.X₂ 0).hom v₂) :=
        ConcreteCategory.congr_hom (sectionMap_degree T U S.g 0) v₂
      _ = (S.g.f 0).hom.app (op U) r := congrArg
        (fun t ↦ (S.g.f 0).hom.app (op U) t)
        (Iso.inv_hom_id_apply (sectionDegreeIso T U S.X₂ 0) r)
      _ = g := hr
      _ = _ := hz.symm
  have hv₁ : R.f.f 1 v₁ = R.X₂.d 0 1 v₂ := by
    apply (ConcreteCategory.bijective_of_isIso (sectionDegreeIso T U S.X₂ 1).hom).1
    calc
      _ = (S.f.f 1).hom.app (op U) ((sectionDegreeIso T U S.X₁ 1).hom v₁) :=
        ConcreteCategory.congr_hom (sectionMap_degree T U S.f 1) v₁
      _ = (S.f.f 1).hom.app (op U) c := congrArg
        (fun t ↦ (S.f.f 1).hom.app (op U) t)
        (Iso.inv_hom_id_apply (sectionDegreeIso T U S.X₁ 1) c)
      _ = (S.X₂.d 0 1).hom.app (op U) r := hc
      _ = (S.X₂.d 0 1).hom.app (op U) ((sectionDegreeIso T U S.X₂ 0).hom v₂) :=
        congrArg (fun t ↦ (S.X₂.d 0 1).hom.app (op U) t)
          (Iso.inv_hom_id_apply (sectionDegreeIso T U S.X₂ 0) r).symm
      _ = _ := (ConcreteCategory.congr_hom (section_d_degree T U S.X₂ 0 1) v₂).symm
  obtain ⟨w, hw, hd⟩ := connecting_cycle R hS 0 z v₂ hv₂ v₁ hv₁
  refine ⟨w, ?_, hd⟩
  change (sectionDegreeIso T U S.X₁ 1).hom (R.X₁.iCycles 1 w) = c
  exact (congrArg (fun t ↦ (sectionDegreeIso T U S.X₁ 1).hom t) hw).trans
    (Iso.inv_hom_id_apply (sectionDegreeIso T U S.X₁ 1) c)

@[irreducible] private def signedElement (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ) (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op U)) : (relativeSectionComplex T U I).X ((q : ℤ) + 1) :=
  (relativeDegreeIso T U I q).inv (a, -b)

set_option backward.isDefEq.respectTransparency false in
private lemma signedElement_raw (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ) (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op U)) :
    relativeFst T U I q (signedElement T U I q a b) = a ∧
      relativeSnd T U I q (signedElement T U I q a b) = -b := by
  unfold signedElement
  have h := Iso.inv_hom_id_apply (relativeDegreeIso T U I q) (a, -b)
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

set_option backward.isDefEq.respectTransparency false in
private lemma signedElement_zero (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : (I.X 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X 0).obj.obj (op U)) :
    torsorSignedA T U I 0 (signedElement T U I 0 a b) = a ∧
      torsorSignedB T U I 0 (signedElement T U I 0 a b) = b := by
  unfold signedElement
  have h := Iso.inv_hom_id_apply (relativeDegreeIso T U I 0) (a, -b)
  constructor
  · erw [signedA_eq]
    exact congrArg Prod.fst h
  · erw [signedB_eq]
    change -(relativeSnd T U I 0 (((relativeDegreeIso T U I 0).inv (a, -b)))) = b
    rw [show relativeSnd T U I 0 (((relativeDegreeIso T U I 0).inv (a, -b))) = -b from
      congrArg Prod.snd h, neg_neg]

set_option backward.isDefEq.respectTransparency false in
private lemma signedElement_one (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : (I.X 2).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X 1).obj.obj (op U)) :
    torsorSignedA T U I 1 (signedElement T U I 1 a b) = a ∧
      torsorSignedB T U I 1 (signedElement T U I 1 a b) = b := by
  unfold signedElement
  have h := Iso.inv_hom_id_apply (relativeDegreeIso T U I 1) (a, -b)
  constructor
  · erw [signedA_one]
    exact congrArg Prod.fst h
  · erw [signedB_one]
    change -(relativeSnd T U I 1 (((relativeDegreeIso T U I 1).inv (a, -b)))) = b
    rw [show relativeSnd T U I 1 (((relativeDegreeIso T U I 1).inv (a, -b))) = -b from
      congrArg Prod.snd h, neg_neg]

set_option backward.isDefEq.respectTransparency false in
private lemma signed_ext_zero (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (x y : (relativeSectionComplex T U I).X 1)
    (ha : torsorSignedA T U I 0 x = torsorSignedA T U I 0 y)
    (hb : torsorSignedB T U I 0 x = torsorSignedB T U I 0 y) : x = y := by
  apply (ConcreteCategory.bijective_of_isIso (relativeDegreeIso T U I 0).hom).1
  apply Prod.ext
  · exact (congrArg (fun f ↦ f x) (signedA_eq T U I)).symm.trans
      (ha.trans (congrArg (fun f ↦ f y) (signedA_eq T U I)))
  · apply neg_injective
    exact (congrArg (fun f ↦ f x) (signedB_eq T U I)).symm.trans
      (hb.trans (congrArg (fun f ↦ f y) (signedB_eq T U I)))

set_option backward.isDefEq.respectTransparency false in
private lemma signed_ext_one (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (x y : (relativeSectionComplex T U I).X 2)
    (ha : torsorSignedA T U I 1 x = torsorSignedA T U I 1 y)
    (hb : torsorSignedB T U I 1 x = torsorSignedB T U I 1 y) : x = y := by
  apply (ConcreteCategory.bijective_of_isIso (relativeDegreeIso T U I 1).hom).1
  apply Prod.ext
  · exact (congrArg (fun f ↦ f x) (signedA_one T U I)).symm.trans
      (ha.trans (congrArg (fun f ↦ f y) (signedA_one T U I)))
  · apply neg_injective
    exact (congrArg (fun f ↦ f x) (signedB_one T U I)).symm.trans
      (hb.trans (congrArg (fun f ↦ f y) (signedB_one T U I)))

set_option backward.isDefEq.respectTransparency false in
private lemma signed_d_zero (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (r : (I.X 0).obj.obj (op U)) :
    (relativeSectionComplex T U I).d 1 2 (signedElement T U I 0 0 r) =
      signedElement T U I 1 0 (-(I.d 0 1).hom.app (op U) r) := by
  let v := signedElement T U I 0 0 r
  have hv := signedElement_zero T U I 0 r
  have hw := signedElement_one T U I 0 (-(I.d 0 1).hom.app (op U) r)
  have hfst : relativeFst T U I 0 v = 0 := (signedElement_raw T U I 0 0 r).1
  have hsnd : relativeSnd T U I 0 v = -r := (signedElement_raw T U I 0 0 r).2
  have hdA := ConcreteCategory.congr_hom (relative_d_fst T U I) v
  change relativeFst T U I 1 ((relativeSectionComplex T U I).d 1 2 v) =
    (I.d 1 2).hom.app (op (Scheme.Etale.mk (𝟙 T))) (relativeFst T U I 0 v) at hdA
  rw [hfst, map_zero] at hdA
  have hdB := ConcreteCategory.congr_hom (relative_d_snd T U I) v
  change relativeSnd T U I 1 ((relativeSectionComplex T U I).d 1 2 v) =
    -((I.X 1).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op
      (relativeFst T U I 0 v) +
      (I.d 0 1).hom.app (op U) (relativeSnd T U I 0 v)) at hdB
  rw [hfst, hsnd, map_zero, zero_add, map_neg, neg_neg] at hdB
  apply signed_ext_one T U I
  · exact (congrArg (fun f ↦ f ((relativeSectionComplex T U I).d 1 2 v))
      (signedA_one T U I)).trans (hdA.trans hw.1.symm)
  · exact (congrArg (fun f ↦ f ((relativeSectionComplex T U I).d 1 2 v))
      (signedB_one T U I)).trans ((congrArg Neg.neg hdB).trans hw.2.symm)

set_option backward.isDefEq.respectTransparency false in
private lemma signedMap_element_zero (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J)
    (a : (I.X 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X 0).obj.obj (op U)) :
    (relativeSectionMap T U f).f 1 (signedElement T U I 0 a b) =
      signedElement T U J 0 ((f.f 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) a)
        ((f.f 0).hom.app (op U) b) := by
  let α := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).map f
  let β := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map f
  let v := signedElement T U I 0 a b
  have hA := ConcreteCategory.congr_hom
    (signedMap_A T T U U I J α β (relativeSectionMap_square T U f) 0) v
  have hB := ConcreteCategory.congr_hom
    (signedMap_B T T U U I J α β (relativeSectionMap_square T U f) 0) v
  have hv := signedElement_zero T U I a b
  have hw := signedElement_zero T U J
    ((f.f 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) a) ((f.f 0).hom.app (op U) b)
  apply signed_ext_zero T U J
  · exact hA.trans ((congrArg (fun t ↦ α.f 1 t) hv.1).trans hw.1.symm)
  · exact hB.trans ((congrArg (fun t ↦ β.f 0 t) hv.2).trans hw.2.symm)

set_option backward.isDefEq.respectTransparency false in
private lemma signedMap_element_one (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J)
    (a : (I.X 2).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X 1).obj.obj (op U)) :
    (relativeSectionMap T U f).f 2 (signedElement T U I 1 a b) =
      signedElement T U J 1 ((f.f 2).hom.app (op (Scheme.Etale.mk (𝟙 T))) a)
        ((f.f 1).hom.app (op U) b) := by
  let α := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).map f
  let β := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map f
  let v := signedElement T U I 1 a b
  have hA := ConcreteCategory.congr_hom
    (signedMap_A T T U U I J α β (relativeSectionMap_square T U f) 1) v
  have hB := ConcreteCategory.congr_hom
    (signedMap_B T T U U I J α β (relativeSectionMap_square T U f) 1) v
  have hv := signedElement_one T U I a b
  have hw := signedElement_one T U J
    ((f.f 2).hom.app (op (Scheme.Etale.mk (𝟙 T))) a) ((f.f 1).hom.app (op U) b)
  apply signed_ext_one T U J
  · exact hA.trans ((congrArg (fun t ↦ α.f 2 t) hv.1).trans hw.1.symm)
  · exact hB.trans ((congrArg (fun t ↦ β.f 1 t) hv.2).trans hw.2.symm)

set_option backward.isDefEq.respectTransparency false in
private lemma relativeConnecting_represents (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (g : (S.X₃.X 0).obj.obj (op U))
    (x : (relativeSectionComplex T U S.X₃).homology 1)
    (hx : TorsorSignedRepresents T U S.X₃ 0 0 g x)
    (r : (S.X₂.X 0).obj.obj (op U))
    (hr : (S.g.f 0).hom.app (op U) r = g)
    (c : (S.X₁.X 1).obj.obj (op U))
    (hc : (S.f.f 1).hom.app (op U) c = (S.X₂.d 0 1).hom.app (op U) r) :
    TorsorSignedRepresents T U S.X₁ 1 0 (-c)
      (relativeConnecting T U S hs 1 x) := by
  obtain ⟨z, hzA, hzB, rfl⟩ := hx
  let R := relativeShortComplex T U S
  have hR := relativeShortComplex_shortExact T U S hs
  let v₃ := R.X₃.iCycles 1 z
  let v₂ := signedElement T U S.X₂ 0 0 r
  let v₁ := signedElement T U S.X₁ 1 0 (-c)
  have hv₂ : R.g.f 1 v₂ = v₃ := by
    change (relativeSectionMap T U S.g).f 1 (signedElement T U S.X₂ 0 0 r) = _
    have he : (relativeSectionMap T U S.g).f 1 (signedElement T U S.X₂ 0 0 r) =
        signedElement T U S.X₃ 0 0 g :=
      (signedMap_element_zero T U S.g 0 r).trans
        (congrArg₂ (fun a b ↦ signedElement T U S.X₃ 0 a b)
          (map_zero ((S.g.f 1).hom.app (op (Scheme.Etale.mk (𝟙 T)))).hom) hr)
    apply he.trans
    exact signed_ext_zero T U S.X₃ _ _
      ((signedElement_zero T U S.X₃ 0 g).1.trans hzA.symm)
      ((signedElement_zero T U S.X₃ 0 g).2.trans hzB.symm)
  have hv₁ : R.f.f 2 v₁ = R.X₂.d 1 2 v₂ := by
    change (relativeSectionMap T U S.f).f 2 (signedElement T U S.X₁ 1 0 (-c)) =
      (relativeSectionComplex T U S.X₂).d 1 2 (signedElement T U S.X₂ 0 0 r)
    calc
      _ = signedElement T U S.X₂ 1
          ((S.f.f 2).hom.app (op (Scheme.Etale.mk (𝟙 T))) 0)
          ((S.f.f 1).hom.app (op U) (-c)) := signedMap_element_one T U S.f 0 (-c)
      _ = signedElement T U S.X₂ 1 0 (-(S.X₂.d 0 1).hom.app (op U) r) :=
        congrArg₂ (fun a b ↦ signedElement T U S.X₂ 1 a b)
          (map_zero ((S.f.f 2).hom.app (op (Scheme.Etale.mk (𝟙 T)))).hom)
          ((map_neg ((S.f.f 1).hom.app (op U)).hom c).trans (congrArg Neg.neg hc))
      _ = _ := (signed_d_zero T U S.X₂ r).symm
  obtain ⟨w, hw, hd⟩ := connecting_cycle R hR 1 z v₂ hv₂ v₁ hv₁
  refine ⟨w, ?_, ?_, hd⟩
  · exact (congrArg (fun t ↦ torsorSignedA T U S.X₁ 1 t) hw).trans
      (signedElement_one T U S.X₁ 0 (-c)).1
  · exact (congrArg (fun t ↦ torsorSignedB T U S.X₁ 1 t) hw).trans
      (signedElement_one T U S.X₁ 0 (-c)).2

set_option backward.isDefEq.respectTransparency false in
private lemma signedRep_unique_one (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : (I.X 2).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X 1).obj.obj (op U))
    (x y : (relativeSectionComplex T U I).homology 2)
    (hx : TorsorSignedRepresents T U I 1 a b x)
    (hy : TorsorSignedRepresents T U I 1 a b y) : x = y := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  obtain ⟨z', ha', hb', rfl⟩ := hy
  have hz : z = z' := (AddCommGrpCat.mono_iff_injective
    ((relativeSectionComplex T U I).iCycles 2)).1 inferInstance
      (signed_ext_one T U I _ _ (ha.trans ha'.symm) (hb.trans hb'.symm))
  exact congrArg (fun w ↦ (relativeSectionComplex T U I).homologyπ 2 w) hz

attribute [local irreducible] TorsorSignedRepresents TorsorSectionRepresents

set_option backward.isDefEq.respectTransparency false in
private lemma raw_boundary_signs :
    DivisorTorsorBoundarySigns (fun (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G) ↦
        relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I) := by
  classical
  refine {
    representative := ?_
    resolutions := ?_
    localization := ?_
    trivial := ?_
    coefficients := ?_
    extensions := ?_
    coefficient_representatives := ?_
    restriction_representatives := ?_
    localization_coefficients := ?_
    localization_restriction := ?_
    connecting_coefficients := ?_
    connecting_restriction := ?_ }
  · intro T Z i _ W hW G I P E h hh
    exact extension_representation T (Scheme.Etale.mk W.ι) I P E h hh
  · intro T W G I J a P
    induction P using Quotient.inductionOn with
    | h P =>
      exact relativeTorsorEquiv_coefficient T (Scheme.Etale.mk W.ι) (𝟙 G) I J a P P.1
        (𝟙 P.1.sheaf.obj) (fun A g t ↦ rfl)
        (relativeSectionMap_square T (Scheme.Etale.mk W.ι) a.hom)
  · exact fun T W I q b x hx ↦
      localization_represents T (Scheme.Etale.mk W.ι) I q b x hx
  · exact fun T W G I g ↦ trivial_boundary T (Scheme.Etale.mk W.ι) I g
  · intro T W S hS I J K a b hab ha hb hs
    let U := Scheme.Etale.mk W.ι
    let R := ShortComplex.mk a b hab
    let hOpen := openShortExact T U R hs
    refine ⟨hOpen, ?_⟩
    intro g
    have hg : (K.cocomplex.d 0 1).hom.app (op U)
        ((K.ι.f 0).hom.app (op U) g) = 0 :=
      congrArg (fun k : S.X₃ ⟶ K.cocomplex.X 1 ↦ k.hom.app (op U) g)
        K.ι_f_zero_comp_complex_d
    obtain ⟨x, hx⟩ := sectionClass_of_closed T U K.cocomplex 0 _ hg
    have ht := trivial_represents T U K g
    have hc : ∀ r : (J.cocomplex.X 0).obj.obj (op U),
        (b.f 0).hom.app (op U) r = (K.ι.f 0).hom.app (op U) g →
        ∃ c : (I.cocomplex.X 1).obj.obj (op U),
          (a.f 1).hom.app (op U) c = (J.cocomplex.d 0 1).hom.app (op U) r ∧
          TorsorSectionRepresents U I.cocomplex 1 c (hOpen.δ 0 1 rfl x) ∧
          TorsorSignedRepresents T U I.cocomplex 1 0 (-c)
            (relativeConnecting T U R hs 1
              (relativeTorsorEquiv T U K (Quotient.mk _ ⟨Sheaf.Torsor.trivial S.X₃, g⟩))) := by
      intro r hr
      have hz : (b.f 1).hom.app (op U) ((J.cocomplex.d 0 1).hom.app (op U) r) = 0 := by
        have hh := ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f.hom.app (op U)) (b.comm 0 1)) r
        change (K.cocomplex.d 0 1).hom.app (op U) ((b.f 0).hom.app (op U) r) =
          (b.f 1).hom.app (op U) ((J.cocomplex.d 0 1).hom.app (op U) r) at hh
        rw [← hh, hr, hg]
      let row := ((R.map (HomologicalComplex.eval _ (.up ℕ) 1)).map
        (etaleSectionFunctor U))
      have hrow : row.ShortExact := ((hs 1).some.map (etaleSectionFunctor U)).shortExact
      obtain ⟨c, hcr⟩ := (ShortComplex.exact_iff_of_hasForget row).1 hrow.exact
        ((J.cocomplex.d 0 1).hom.app (op U) r) hz
      refine ⟨c, hcr, ?_, ?_⟩
      · exact openConnecting_represents T U R hOpen _ x hx r hr c hcr
      · exact relativeConnecting_represents T U R hs _ _ ht r hr c hcr
    let row := ((R.map (HomologicalComplex.eval _ (.up ℕ) 0)).map
      (etaleSectionFunctor U))
    have hrow : row.ShortExact := ((hs 0).some.map (etaleSectionFunctor U)).shortExact
    obtain ⟨r, hr⟩ := hrow.surjective_g ((K.ι.f 0).hom.app (op U) g)
    obtain ⟨c, hcr, hco, hcrel⟩ := hc r hr
    have he := signedRep_unique_one T U I.cocomplex 0 (-c) _ _ hcrel
      (localization_represents T U I.cocomplex 1 c _ hco)
    refine ⟨x, hx, he, ?_⟩
    intro r hr
    obtain ⟨c, hcr, hco, hcrel⟩ := hc r hr
    exact ⟨c, hcr, hco, hcrel, localization_represents T U I.cocomplex 1 c _ hco⟩
  · intro T W G I P E h h' hh hh' a a' ha ha'
    obtain ⟨x, hd, hr⟩ := Sheaf.Torsor.difference_of_equivariant_lifts
      (MorphismProperty.Over.mkIdTerminal @Etale T) P.1
      (I.cocomplex.X 0) (I.cocomplex.X 1) (I.cocomplex.d 0 1) (I.ι.f 0)
      (extensionLiftMap T E h) (extensionLiftMap T E h')
      (fun A g t ↦ by rw [extensionLiftMap_vadd, hh])
      (fun A g t ↦ by rw [extensionLiftMap_vadd, hh'])
      (integerSectionEquiv T (I.cocomplex.X 1) a)
      (integerSectionEquiv T (I.cocomplex.X 1) a')
      (extension_d_generator T I E h a ha)
      (extension_d_generator T I E h' a' ha')
    refine ⟨x, ?_, (hr (op (Scheme.Etale.mk W.ι)) P.2).symm⟩
    rw [integerSectionEquiv_eval, integerSectionEquiv_eval] at hd
    exact hd.symm
  · intro T W I J f q a b x hx
    exact signedRep_map T T (Scheme.Etale.mk W.ι) (Scheme.Etale.mk W.ι) I J
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).map f)
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).map f)
      (relativeSectionMap_square T (Scheme.Etale.mk W.ι) f) q a b x hx
  · intro T T' h _ W I J f q a b x hx
    exact signedRep_map T T' (Scheme.Etale.mk W.ι) (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) I J
      (globalResolutionSectionTransfer h I J f) (openResolutionSectionTransfer h I J f W)
      (relativeTransfer_square h W I J f) q a b x hx
  · intro T W I J f q
    exact coneLocalization_natural _ _ _ _
      (relativeSectionMap_square T (Scheme.Etale.mk W.ι) f) q
  · intro T T' h _ W I J f q
    exact coneLocalization_natural _ _ _ _ (relativeTransfer_square h W I J f) q
  · exact fun T W S S' hs hs' f q ↦
      relativeConnecting_coefficient_naturality T (Scheme.Etale.mk W.ι) S S' hs hs' f q
  · exact fun T T' h _ W S S' hs hs' f q ↦
      relativeConnecting_pullback_naturality h W S S' hs hs' f q

-- Keep the public statement on the original canonical instances.
attribute [-instance] torsorBoundaryHasSheafify torsorBoundaryWEqualsLocallyBijective
  torsorBoundarySectionPreservesZero torsorBoundaryComplexSectionsPreservesZero
  torsorBoundaryIdentityForget torsorBoundaryIdentityForgetAdditive
  torsorBoundaryIdentityForgetHomology

set_option backward.isDefEq.respectTransparency false in
/-- The canonical relative torsor classification admits the specified extension
representatives and the two boundary signs, simultaneously in all resolution models.
The classification uses the raw lifting cocycle. Its negative forgetful image is
the Ext-normalized torsor class; the final conjunct specifies the representatives.
The normalized classification in `relative_torsor_cohomology` is the negative of this one.
Source: Stacks Tag 03AJ; blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, clause (a)
(blueprint: lem-pur-divisor-torsor-boundary-signs).

STATEMENT-DISPUTED: the original positive forgetful clause conflicts with the raw
representatives and the proved Ext comparison. The statement below corrects that clause.

Proof:
1. Use the raw lifting-cocycle equivalence. The frame forget-normalization theorem
sends its class to minus the torsor H1 class; hence the displayed negative forgetful
image. The proved raw-class naturality gives coefficient and pullback compatibility.
2. The presentation map t ↦ h(generator(t)) is equivariant with augmentation as
its action increment. Its image in resolution cycles is invariant and glues to a
global cycle s. It is an equivariant isomorphism with the lifting torsor of s.
The constant-sheaf adjunction gives a from iCycles(s). Uniqueness in the extension
presentation proves projection followed by a equals dh. The raw classification
presentation formula gives the required signed representative (a,h(section)).
3. Apply the global difference theorem for two equivariant lifting maps to h and
h'. It supplies x with derivative a'-a and restriction h'(section)-h(section).
4. Apply the shift short-complex isomorphism to a section cycle, then the shifted
cone inclusion. Its signed coordinates are (0,-b). The quotient commutes with both
maps. The zero lifting presentation computes the trivial pair as (0,g), and
uniqueness of its signed coordinates identifies its class with minus the boundary.
5. Evaluate the specified splittings and extend by zero to get a short exact open
section sequence. A lift r of the augmented g exists in degree zero. Its derivative
lies in the kernel of the degree-one quotient, so choose c with a(c)=dr. Mathlib's
concrete boundary formula computes the ordinary boundary as [c]. The relative
lift (0,r) differentiates to (0,-dr), so the same formula computes the relative
boundary as [(0,-c)]. This is the localization representative of [c], and the
coordinate isomorphism proves equality of the two classes, for every lift r.
6. Cone maps act componentwise on the signed coordinates. Apply cyclesMap and
quotient naturality to obtain the representative transport formulas. Naturality
of cone inclusions and the shift homology isomorphism gives localization squares.
The proved relativeConnecting naturality supplies the last two squares. Resolution
comparisons are the identity-coefficient instance of raw-class naturality. -/
theorem divisor_torsor_boundary_signs :
    ∃ e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1,
    ((∀ T W G I,
      e T W G I (Quotient.mk _
        ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op (Scheme.Etale.mk W.ι))) 0⟩) = 0) ∧
    (∀ T W G I (c : ResolutionSectionCanonicalComparison G I)
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)),
      -relativeForgetH1 T W G I c (e T W G I (Quotient.mk _ P)) =
        Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
          (Quotient.mk _ P.1)) ∧
    (∀ (T : Scheme.{u}) (W : T.Opens)
      (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : G ⟶ G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.Hom J f) (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
      (Q : Sheaf.Torsor G') (q : Sheaf.Torsor.ContractedProductPresentation.{u, u} T f P.1 Q),
      HomologicalComplex.homologyMap
          (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1
          (e T W G I (Quotient.mk _ P)) =
        e T W G' J (Quotient.mk _ ⟨Q, q.quotient (op (Scheme.Etale.mk W.ι)) P.2 0⟩)) ∧
    (∀ (T T' : Scheme.{u}) (h : T' ⟶ T) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.cocomplex ⟶
        ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
      (_ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)) (Q : Sheaf.Torsor G')
      (b : P.1.sheaf.obj ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
      (_hb : ∀ (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.1.sheaf.obj.obj A),
        b.app A (P.1.vadd A g t) =
          Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj A.unop))
            (f.hom.app A g) (b.app A t)),
      HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) 1
          (e T W G I (Quotient.mk _ P)) =
        e T' (h ⁻¹ᵁ W) G' J (Quotient.mk _
          ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
            (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩))) ∧
    DivisorTorsorBoundarySigns e := by
  classical
  let e := fun (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G) ↦
      relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I
  refine ⟨e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun T W G I ↦ relativeTorsorEquiv_zero T (Scheme.Etale.mk W.ι) I
  · intro T W G I c P
    change -c.globalEquiv 1
      (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)).hom
        (homologyMap (relativeForgetComplex T (Scheme.Etale.mk W.ι) I.cocomplex) 1
          (relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I (Quotient.mk _ P)))) = _
    let hT := MorphismProperty.Over.mkIdTerminal @Etale T
    let : Injective (I.cocomplex.X 0) := I.injective 0
    obtain ⟨s, ⟨ε⟩⟩ := Sheaf.Torsor.exists_equiv_lifts (G := G)
      (ι := I.ι.f 0) (d := I.cocomplex.toCycles 0 1) hT
      (resolutionLiftSequence_shortExact T I) P.1
    rw [relativeTorsorEquiv_presentation T (Scheme.Etale.mk W.ι) I P s ε,
      relativeFrameClass_forget, neg_neg]
    have hp : (Quotient.mk _ P.1 : _root_.Quotient (Sheaf.Torsor.setoid (G := G))) =
        Quotient.mk _ (Sheaf.Torsor.lifts (G := G) hT (resolutionLiftSequence_shortExact T I) s) :=
      Quotient.sound ⟨ε⟩
    rw [hp, Sheaf.Torsor.classH1_lifts (G := G)
      (ι := I.ι.f 0) (d := I.cocomplex.toCycles 0 1)]
    rfl
  · intro T W G G' f I J a P Q q
    let σ : P.1.sheaf.obj ⟶ Q.sheaf.obj :=
      { app A := TypeCat.ofHom fun t ↦ q.quotient A t 0
        naturality A B k := by
          ext t
          change q.quotient B (P.1.sheaf.obj.map k t) 0 =
            Q.sheaf.obj.map k (q.quotient A t 0)
          rw [q.quotient_natural, map_zero] }
    apply relativeTorsorEquiv_coefficient T (Scheme.Etale.mk W.ι) f I J a P Q σ
      (fun A g t ↦ ?_) (relativeSectionMap_square T (Scheme.Etale.mk W.ι) a.hom)
    change q.quotient A (P.1.vadd A g t) 0 = Q.vadd A (f.hom.app A g) (q.quotient A t 0)
    calc
      _ = q.quotient A t (f.hom.app A g) := by
        simpa only [sub_self] using q.quotient_invariant A g t (f.hom.app A g)
      _ = _ := by simpa only [zero_add] using q.quotient_vadd A t 0 (f.hom.app A g)
  · intro T T' h W G G' f I J a ha P Q b hb
    exact relativeTorsorEquiv_transfer h W f I J a ha P Q b hb
      (relativeTransfer_square h W I.cocomplex J.cocomplex a)
  · exact raw_boundary_signs

end AlgebraicGeometry.Etale
