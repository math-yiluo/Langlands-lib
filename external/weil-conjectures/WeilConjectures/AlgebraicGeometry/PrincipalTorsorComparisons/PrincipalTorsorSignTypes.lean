/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.DivisorTorsorBoundarySigns
public import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedSections
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The inverse-section pushout and its Yoneda sign

The comparison is characterized on every injective-resolution cocycle. Its naturality
is expressed for arbitrary coefficient lifts and for etale restriction of cocycles.
The formula uses the actual open-closed sequence, not a freely supplied sequence.

## References

* Stacks Tags 03AJ, 0A45, 06XU
* Stacks 0G78 and 03AJ
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open HomologicalComplex

namespace AlgebraicGeometry.Etale

/-- The closed term of integral localization, cached to keep the normalized Ext types small.
This is the actual closed term of the open--closed sequence. -/
def principalTorsorClosedTerm {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h)
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).X₃

/-- The localization sequence on the integral constant sheaf. Its end terms
are canonically `j_! Z_W` and `i_* Z_Z`, by constant inverse-image comparison. -/
def principalTorsorLocalization {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  let L :=
    openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
      (disjoint_range_of_range_eq_compl W.ι i h)
      ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  { X₁ := L.X₁
    X₂ := L.X₂
    X₃ := principalTorsorClosedTerm i W h
    f := L.f
    g := L.g
    zero := L.zero }

/-- Models of the two adjunction comparisons used in the framed-torsor calculation.
The accompanying normalization fixes their values on all cocycles, so no arbitrary
identification of Ext with cohomology is being used. -/
structure PrincipalTorsorComparisons where
  openSection : ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
    ((principalTorsorLocalization i W h).X₁ ⟶ G) ≃+
      G.obj.obj (op (Scheme.Etale.mk W.ι))
  relative : ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (q : ℕ),
    Ext (principalTorsorLocalization i W h).X₃ G (q + 1) ≃+
      relativeCohomology T (Scheme.Etale.mk W.ι) I ((q : ℤ) + 1)
  support : ∀ T : Scheme.{u}, RelativeCone.System T.smallEtaleTopology
    (fun {_ _} f ↦ IsOpenImmersion f.left)

/-- The normalized comparison to the right-derived kernel, with its source and target
fixed explicitly before using it in the splice formula. -/
def PrincipalTorsorComparisons.toSupport (C : PrincipalTorsorComparisons.{u})
    (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (q : ℕ) :
    relativeCohomology T (Scheme.Etale.mk W.ι) I (q : ℤ) ⟶
      ((Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1}
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from
          (Scheme.Etale.mk W.ι))).rightDerived q).obj G :=
  (((C.support T).realization
    ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι))
    (inferInstance : IsOpenImmersion W.ι) I).e q).hom

/-- The open adjunction is natural, takes the inclusion to one, and the supported-Hom
comparison sends a cocycle `z` to `(z p(1),0)`. This is a characterization, not an
assumption added to the framed-torsor theorem. -/
def PrincipalTorsorComparisons.Normalized (C : PrincipalTorsorComparisons.{u}) : Prop :=
  (∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (A B : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : A ⟶ B) (v : (principalTorsorLocalization i W h).X₁ ⟶ A),
    C.openSection T Z i W h B (v ≫ f) =
      f.hom.app (op (Scheme.Etale.mk W.ι)) (C.openSection T Z i W h A v)) ∧
  (∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ),
    C.openSection T Z i W h ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      (principalTorsorLocalization i W h).f = torsorExtensionOne T (Scheme.Etale.mk W.ι)) ∧
  (∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (q : ℕ)
    (z : (principalTorsorLocalization i W h).X₃ ⟶ I.cocomplex.X (q + 1))
    (hz : z ≫ I.cocomplex.d (q + 1) (q + 1 + 1) = 0),
    TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex q
      (((principalTorsorLocalization i W h).g ≫ z).hom.app
        (op (Scheme.Etale.mk (𝟙 T))) (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))) 0
      (C.relative T Z i W h G I q (I.extMk z (q + 1 + 1) rfl hz)))

/-- Naturality of the normalized comparisons under coefficient maps and arbitrary
resolution lifts. The second clause gives etale restriction on cocycles: the equation
on evaluated supported cocycles is precisely the restriction of `z p(1)`. -/
def PrincipalTorsorComparisons.Natural (C : PrincipalTorsorComparisons.{u}) : Prop :=
  (∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ G')
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (f : I.cocomplex ⟶ J.cocomplex)
    (_hf : I.ι.f 0 ≫ f.f 0 = a ≫ J.ι.f 0) (q : ℕ)
    (x : Ext (principalTorsorLocalization i W h).X₃ G (q + 1)),
    C.relative T Z i W h G' J q (x.comp (Ext.mk₀ a) (add_zero _)) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f) ((q : ℤ) + 1)
        (C.relative T Z i W h G I q x)) ∧
  (∀ (T Z T' Z' : Scheme.{u}) (v : T' ⟶ T) [Etale v]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (w : Z' ⟶ Z) (_sq : IsPullback w i' i v)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (h' : Set.range i'.base = (Set.range (v ⁻¹ᵁ W).ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (f : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} v).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (q : ℕ)
    (z : (principalTorsorLocalization i W h).X₃ ⟶ I.cocomplex.X (q + 1))
    (hz : z ≫ I.cocomplex.d (q + 1) (q + 1 + 1) = 0)
    (z' : (principalTorsorLocalization i' (v ⁻¹ᵁ W) h').X₃ ⟶
      J.cocomplex.X (q + 1))
    (hz' : z' ≫ J.cocomplex.d (q + 1) (q + 1 + 1) = 0)
    (_hres : ((principalTorsorLocalization i' (v ⁻¹ᵁ W) h').g ≫ z').hom.app
        (op (Scheme.Etale.mk (𝟙 T'))) (torsorExtensionOne T' (Scheme.Etale.mk (𝟙 T'))) =
      (globalResolutionSectionTransfer v I.cocomplex J.cocomplex f).f (q + 1)
        (((principalTorsorLocalization i W h).g ≫ z).hom.app
          (op (Scheme.Etale.mk (𝟙 T))) (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))))),
    C.relative T' Z' i' (v ⁻¹ᵁ W) h' G' J q (J.extMk z' (q + 1 + 1) rfl hz') =
      homologyMap (relativeTransfer v W I.cocomplex J.cocomplex f) ((q : ℤ) + 1)
        (C.relative T Z i W h G I q (I.extMk z (q + 1 + 1) rfl hz)))

/-- The pushout assertion for the specified extension, and the signed splice in the
actual right-derived kernel of restriction. The horseshoe data and cocycle `x` are
arbitrary computational models of the coefficient boundary, not extra assumptions on
coefficients. -/
def PrincipalTorsorComparisons.Formula (C : PrincipalTorsorComparisons.{u}) : Prop :=
  ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (P : Sheaf.Torsor G)
    (e : P.sheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (s : P.sheaf.obj.obj (op (Scheme.Etale.mk W.ι)))
    (g : G.obj.obj (op (Scheme.Etale.mk W.ι)))
    (_hs : s = P.vadd (op (Scheme.Etale.mk W.ι)) g
      (P.sheaf.obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op e))
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : G ⟶ E) (b : E ⟶ (principalTorsorLocalization i W h).X₃)
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (F : P.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1})
    (_hF : ∀ (U : T.Etaleᵒᵖ) (x : G.obj.obj U) (p : P.sheaf.obj.obj U),
      @id (E.obj.obj U) (F.app U (P.vadd U x p)) = F.app U p + a.hom.app U x)
    (_hbF : ∀ (U : T.Etaleᵒᵖ) (p : P.sheaf.obj.obj U),
      b.hom.app U (F.app U p) = (principalTorsorLocalization i W h).g.hom.app U
        (torsorExtensionOne T U.unop))
    (_hFs : @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
      (F.app (op (Scheme.Etale.mk W.ι)) s) = 0),
    (∃ hL : (principalTorsorLocalization i W h).ShortExact,
      hE.extClass = hL.extClass.comp
        (Ext.mk₀ ((C.openSection T Z i W h G).symm (-g))) (add_zero 1)) ∧
    (∀ (H K : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (aK : H ⟶ K) (bK : K ⟶ G) (habK : aK ≫ bK = 0)
      (hK : (ShortComplex.mk aK bK habK).ShortExact)
      (I : InjectiveResolution H) (J : InjectiveResolution K) (L : InjectiveResolution G)
      (α : I.cocomplex ⟶ J.cocomplex) (β : J.cocomplex ⟶ L.cocomplex)
      (hαβ : α ≫ β = 0)
      (_hα : I.ι ≫ α = (CochainComplex.single₀ _).map aK ≫ J.ι)
      (_hβ : J.ι ≫ β = (CochainComplex.single₀ _).map bK ≫ L.ι)
      (_hsplit : ∀ n : ℕ, Nonempty (((ShortComplex.mk α β hαβ).map
        (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)),
      ∃ hOpen : (torsorOpenShortComplex T (Scheme.Etale.mk W.ι)
          (ShortComplex.mk α β hαβ)).ShortExact,
        ∀ (x : (relativeSections (Scheme.Etale.mk W.ι) L.cocomplex).homology 0)
          (_hx : TorsorSectionRepresents (Scheme.Etale.mk W.ι) L.cocomplex 0
            ((L.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) x),
        (C.toSupport T W H I 2)
          (C.relative T Z i W h H I 1 (hE.extClass.comp hK.extClass (rfl : 1 + 1 = 2))) =
          -((C.toSupport T W H I 2)
            (torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 1
              (hOpen.δ 0 1 rfl x))))

end AlgebraicGeometry.Etale
