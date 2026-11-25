/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow

/-!
# Constructibility of ordinary finite-coefficient pro-etale direct images

Source: Stacks Project, Tags 09AK, 09AL and 09A6; Bhatt--Scholze,
Theorem 6.7.1 and the finite-coefficient part of Lemma 6.7.2
(blueprint: lem-sf-finite-proetale-pushforward-constructible).

The fixed-module presentation uses the published canonical realization of modules over
constant coefficient sheaves. Constructibility is intrinsic and no Tor bound is imposed.
The comparison arrow is the mate of the exact derived pullback comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Termwise descent of the canonical commuting inverse images, in the direction
`nu_Y^* f_proet^* ≅ f_et^* nu_X^*` used to form the direct-image mate.
Source: Stacks Project, Tag 09A6, preceding paragraph
(blueprint: lem-sf-finite-proetale-pushforward-constructible). -/
def finitePushforwardDerivedPullbackComparison (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical ordinary total derived direct-image comparison, defined as the
counit mate of the specified exact pullback comparison. Thus its component is the
adjoint transpose of the pulled-back etale counit after that comparison; there is no
choice of a morphism or of an isomorphism between the endpoints.
Source: Stacks Project, Tag 09A6, lemma-morphism-comparison
(blueprint: lem-sf-finite-proetale-pushforward-constructible). -/
def finitePushforwardDerivedComparison (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.rightDerivedLowerStar (ModuleCat.{u + 1} B) f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor :=
  (mateEquiv
    ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
      (Etale.upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctorIsoMapDerivedCategory)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
      (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctorIsoMapDerivedCategory)
    (finitePushforwardDerivedPullbackComparison B f).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_mate_change_adjunction
    {A D E F : Type*} [Category A] [Category D] [Category E] [Category F]
    {l : A ⥤ D} {r : D ⥤ A} {p : E ⥤ F} {t : F ⥤ E}
    {a : A ⥤ E} {b : D ⥤ F}
    (e e' : l ⊣ r) (d d' : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) (K : D)
    (h : IsIso ((mateEquiv e' d' σ.hom).app K)) :
    IsIso ((mateEquiv e d σ.hom).app K) := by
  let c := conjugateIsoEquiv e e' (Iso.refl l)
  let q := conjugateIsoEquiv d d' (Iso.refl p)
  have hh := mateEquiv_whiskerTop_conjugateEquiv e e' d d'
    (𝟙 l) (𝟙 p) σ.hom σ.hom (by ext; simp)
  have ht := congrArg (fun w : TwoSquare r b a t ↦ w.app K) hh
  change a.map (c.hom.app K) ≫ (mateEquiv e' d' σ.hom).app K =
    (mateEquiv e d σ.hom).app K ≫ q.hom.app (b.obj K) at ht
  have : IsIso ((mateEquiv e d σ.hom).app K ≫ q.hom.app (b.obj K)) := by
    rw [← ht]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (q.hom.app (b.obj K))

/-- A bounded complex with intrinsically constructible finite-coefficient cohomology
has bounded constructible etale origin, and ordinary direct image along a morphism
of finite-type schemes over a field is bounded and intrinsically constructible.
The comparison after any chosen realization is the specified counit mate followed
by the direct image of that realization.
Source: Stacks Project, Tags 09AL, 09AK and 09A6; Bhatt--Scholze, Theorem 6.7.1 and
finite-coefficient Lemma 6.7.2
(blueprint: lem-sf-finite-proetale-pushforward-constructible).

Proof:
1. A field is Noetherian. The finite-type structure maps make X and Y Noetherian by
`lem-weil-pbc-finite-type-over-noetherian`. Every open of X is quasi-compact by
`lem-weil-pbc-noetherian-open-subscheme-noetherian`. Apply this to preimages of affine
opens under f and its diagonal to obtain qcqs, without separatedness.
2. Choose cohomological bounds, taking [0,0] for the zero object. Apply
`lem-weil-pbc-finite-ring-constructible-derived-origin` to the intrinsic hypothesis to
obtain a bounded constructible etale L and an isomorphism alpha : nu_X^* L ≅ C.
Its interval reflection also gives boundedness below for L.
3. Apply `proposition-six-operations-dctf--2` to L with the given annihilator m.
The finite-type hypotheses, mB = 0 and invertibility in k give bounded constructibility
of the ordinary etale direct image; no separatedness is required.
4. Apply `lem-weil-pbc-comparison-direct-image-canonical-mate` using qcqs and boundedness
below. Under the fully faithful inclusion of D+ this is exactly the displayed unbounded
counit mate. Compose with Rf_proet(alpha) to obtain the canonical comparison for C.
5. Apply the forward direction and interval preservation of
`lem-weil-pbc-finite-ring-constructible-derived-origin` on Y to the etale direct image.
Transport its constructible cohomology and finite cohomological interval through the
isomorphism from step 4. Restricting the isomorphism to each stratum transports the local
constant finite models. No finite Tor amplitude is used at any step. -/
theorem finite_proetale_pushforward_constructible
    (k : Type u) [Field k] (B : Type (u + 1)) [CommRing B] [Finite B]
    (m : ℕ) (hm : 0 < m) (hB : (m : B) = 0) (hk : IsUnit (m : k))
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    (C : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hC : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X B
      ((DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) i).obj C))
    (hCb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) i).obj C)) :
    ∃ L : Etale.DerivedCategoryModule B X,
      Etale.DerivedCategory.isBoundedConstructible B X L ∧
      ∃ α : (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L ≅ C,
        IsIso ((finitePushforwardDerivedComparison B f).app L ≫
          (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.map α.hom) ∧
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf Y B
          ((DerivedCategory.homologyFunctor
            (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B)) i).obj
              ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.obj C))) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((DerivedCategory.homologyFunctor
            (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B)) i).obj
              ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.obj C)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  have : QuasiCompact f := inferInstance
  have : QuasiSeparated f := ⟨inferInstance⟩
  have hb : _root_.DerivedCategory.TStructure.t.bounded C := by
    obtain ⟨a, b, _, hv⟩ := hCb
    exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff C a).2
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff C b).2 (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hinput : (Etale.DerivedCategory.isBoundedConstructible B X).map
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory C := by
    rw [← exceptionalTransport_constructible_comparison B X]
    exact ⟨hb, hC⟩
  obtain ⟨L, hL, ⟨α⟩⟩ := hinput
  have hcoeff : Etale.IsSmoothBaseChangeCoefficients m B (Spec (.of k)) :=
    ⟨hm, inferInstance, hB, by simpa using hk.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have hN := Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    k B m hcoeff aX aY f hf L hL
  obtain ⟨a, b, _, hv⟩ := hL.2
  have : L.IsGE a := (_root_.DerivedCategory.isGE_iff L a).2
    (fun i hi ↦ hv i (Or.inl hi))
  have hmate : IsIso ((finitePushforwardDerivedComparison B f).app L) := by
    apply isIso_mate_change_adjunction _
      ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} B) f).mapDerivedCategoryRightDerivedAdjunction) _
      ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} B) f).mapDerivedCategoryRightDerivedAdjunction)
    have hh := unboundedDirectImageComparison_boundedBelow B f L a
    simpa only [unboundedDirectImageComparisonMap, Adjunction.homEquiv_unit,
      mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.comp_obj, Functor.comp_map, Functor.map_comp, Functor.map_id,
      Functor.id_obj, Functor.id_map, Category.id_comp, Category.comp_id, Category.assoc,
      finitePushforwardDerivedPullbackComparison, unboundedDirectImagePullbackIso] using hh
  have hiso : IsIso ((finitePushforwardDerivedComparison B f).app L ≫
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.map α.hom) := inferInstance
  let β := asIso ((finitePushforwardDerivedComparison B f).app L ≫
    (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.map α.hom)
  have houtput := (ObjectProperty.prop_map_obj
    (Etale.DerivedCategory.isBoundedConstructible B Y)
    (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory hN)
  have houtput' := ((Etale.DerivedCategory.isBoundedConstructible B Y).map
    (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory).prop_of_iso β houtput
  rw [← exceptionalTransport_constructible_comparison B Y] at houtput'
  refine ⟨L, hL, α, hiso, houtput'.2, ?_⟩
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := houtput'.1
  refine ⟨min c d, max c d, min_le_max, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ c).1 hc i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ d).1 hd i
      (lt_of_le_of_lt (le_max_right _ _) hi)

end AlgebraicGeometry.ProEtale
