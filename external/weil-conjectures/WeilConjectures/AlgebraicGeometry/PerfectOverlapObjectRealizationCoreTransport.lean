/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

private theorem cancel_iso_pasting {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (s : D ≅ B)
    (g : D ⟶ E) (h : E ⟶ D) (gh : g ≫ h = 𝟙 D) :
    f = 𝟙 A ≫ f ≫ s.inv ≫ g ≫ 𝟙 E ≫ h ≫ s.hom := by
  simp only [Category.id_comp, Category.comp_id,
    ← Category.assoc, gh, Category.comp_id, Iso.inv_hom_id]
section

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- Construct a simultaneous diagram from restricted pullbacks and site equivalences.
Open restriction is a localization, so its fully faithful precomposition functor lifts
both overlap comparisons and their coherence from the global restriction diagram. -/
noncomputable def schemeComparisonFromRestrictions
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    SchemeTwoOpenComparisonDiagram X Y g U V P Q := by
  let S (W : X.Opens) := (overlapSiteInverse W).mapDerivedCategory
  let H (W : Y.Opens) (T : X.Opens) (hT : T ≤ g ⁻¹ᵁ W) :=
    derivedPullback (g.resLE W T hT) ⋙ S T
  let HU := H U P hP
  let HV := H V Q hQ
  let HW := H (U ⊓ V) (P ⊓ Q) (by
    intro x hx
    exact ⟨hP hx.1, hQ hx.2⟩)
  let β (W : Y.Opens) (T : X.Opens) (hT : T ≤ g ⁻¹ᵁ W) :
      derivedPullback g ⋙
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) T).mapDerivedCategory ≅
        (schemeOpenRestriction Y W).mapDerivedCategory ⋙ H W T hT :=
    perfectOverlapRestrictionBeta g W T hT
  let TU := (schemeOpenRestriction Y U).mapDerivedCategory
  let TV := (schemeOpenRestriction Y V).mapDerivedCategory
  let T := DerivedCategory (SheafOfModules.{u}
    ((moduleRings X.toRingedSpace).over (P ⊓ Q)))
  have : TU.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage TU) :=
    schemeDerivedOpenRestriction_isLocalization Y U
  have : TV.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage TV) :=
    schemeDerivedOpenRestriction_isLocalization Y V
  have := Localization.full_whiskeringLeft TU
    ((MorphismProperty.isomorphisms _).inverseImage TU) T
  have := Localization.faithful_whiskeringLeft TU
    ((MorphismProperty.isomorphisms _).inverseImage TU) T
  have := Localization.full_whiskeringLeft TV
    ((MorphismProperty.isomorphisms _).inverseImage TV) T
  have := Localization.faithful_whiskeringLeft TV
    ((MorphismProperty.isomorphisms _).inverseImage TV) T
  refine ⟨comparisonFromRestrictions (derivedPullback g) TU TV _ _ _ _ _ _ _ _ _ _ _ _
    HU HV HW (β U P hP) (β V Q hQ) (β (U ⊓ V) (P ⊓ Q) _)⟩

/-- The first local comparison field is the fixed restriction/pullback map.
This is the first projection of the comparison diagram constructor. -/
theorem schemeComparisonFromRestrictions_betaU
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    (schemeComparisonFromRestrictions g U V P Q hP hQ).toDiagram.βU =
      perfectOverlapRestrictionBeta g U P hP := by
  rfl

/-- The second local comparison field is the fixed restriction/pullback map.
This is the second projection of the comparison diagram constructor. -/
theorem schemeComparisonFromRestrictions_betaV
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    (schemeComparisonFromRestrictions g U V P Q hP hQ).toDiagram.βV =
      perfectOverlapRestrictionBeta g V Q hQ := by
  rfl

/-- The intersection comparison field is the fixed restriction/pullback map.
For the intersection, the required inclusion is the conjunction of the two
given inclusions. -/
theorem schemeComparisonFromRestrictions_betaW
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    let hW : P ⊓ Q ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hx ↦ ⟨hP hx.1, hQ hx.2⟩
    (schemeComparisonFromRestrictions g U V P Q hP hQ).toDiagram.βW =
      perfectOverlapRestrictionBeta g (U ⊓ V) (P ⊓ Q) hW := by
  rfl

/-- The first-open functor of the comparison diagram is restricted pullback
followed by the inverse open-site equivalence. -/
theorem schemeComparisonFromRestrictions_HU
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    (schemeComparisonFromRestrictions g U V P Q hP hQ).toDiagram.HU =
      derivedPullback (g.resLE U P hP) ⋙ (overlapSiteInverse P).mapDerivedCategory := by
  rfl

/-- The intersection functor of the comparison diagram is the fixed
restricted pullback followed by the inverse open-site equivalence. -/
theorem schemeComparisonFromRestrictions_HW
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    let hW : P ⊓ Q ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hx ↦ ⟨hP hx.1, hQ hx.2⟩
    (schemeComparisonFromRestrictions g U V P Q hP hQ).toDiagram.HW =
      derivedPullback (g.resLE (U ⊓ V) (P ⊓ Q) hW) ⋙
        (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory := by
  rfl

/-- The fixed pullback-composition comparison on a restricted two-step map.
The named definition keeps the geometric equality and its derived transport
outside the larger two-open transport record. -/
noncomputable def perfectOverlapCompositeLocalIso
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (W : Y₀.Opens) :
    let hP : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    derivedPullback (f ∣_ W) ⋙
      derivedPullback (g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP) ≅
        derivedPullback (gf ∣_ W) := by
  intro hP
  have hcomp : g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP ≫ (f ∣_ W) = gf ∣_ W := by
    apply (cancel_mono W.ι).1
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
  exact perfectHomComposition _ _ ≪≫
    eqToIso (congrArg (fun a ↦ derivedPullback a) hcomp)

/-- Construct the transport data for two composable scheme maps.
The restricted composites agree after their open inclusions; pullback composition gives
kappa. Set theta equal to kappa, the supplied local isomorphism, and the site comparison. -/
noncomputable def transportDataOfComposite
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    let P := gf ⁻¹ᵁ U
    let Q := gf ⁻¹ᵁ V
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P).mapDerivedCategory
    let RV := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q).mapDerivedCategory
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let LV := (overlapSiteInverse Q).mapDerivedCategory
    TwoOpenTransportData (SchemeTwoOpenComparisonDiagram X Y g (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) P Q)
      (fun d ↦ d.toDiagram.HU) (fun d ↦ d.toDiagram.HV)
      (derivedPullback (f ∣_ U)) (derivedPullback (f ∣_ V))
      (derivedPullback (gf ∣_ U)) (derivedPullback (gf ∣_ V)) LU LV
      (schemeOpenRestriction X P).mapDerivedCategory
      (schemeOpenRestriction X Q).mapDerivedCategory RU RV A B E φU φV := by
  let hP (W : Y₀.Opens) : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let d := schemeComparisonFromRestrictions g (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (gf ⁻¹ᵁ U) (gf ⁻¹ᵁ V) (hP U) (hP V)
  let κ (W : Y₀.Opens) :
      derivedPullback (f ∣_ W) ⋙
          (derivedPullback (g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) (hP W)) ⋙
            (overlapSiteInverse (gf ⁻¹ᵁ W)).mapDerivedCategory) ≅
        derivedPullback (gf ∣_ W) ⋙
          (overlapSiteInverse (gf ⁻¹ᵁ W)).mapDerivedCategory := by
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (perfectOverlapCompositeLocalIso f g gf hgf W) _
  exact {
    d := d
    κU := κ U
    κV := κ V
    siteU := openSiteReturnIso X (gf ⁻¹ᵁ U)
    siteV := openSiteReturnIso X (gf ⁻¹ᵁ V)
    θU := (κ U).app A ≪≫ (overlapSiteInverse (gf ⁻¹ᵁ U)).mapDerivedCategory.mapIso φU ≪≫
      (openSiteReturnIso X (gf ⁻¹ᵁ U)).app E
    θV := (κ V).app B ≪≫ (overlapSiteInverse (gf ⁻¹ᵁ V)).mapDerivedCategory.mapIso φV ≪≫
      (openSiteReturnIso X (gf ⁻¹ᵁ V)).app E
    hθU := rfl
    hθV := rfl }

/-- The diagram field of composite transport is the restriction diagram for the
second map.
Source: Stacks Project, Tags 08DW and 0D5S. The composite transport first
constructs the restriction comparison for `g` on both inverse-image opens; its
remaining fields add the two pullback-composition isomorphisms and the local
object identifications. Projecting the diagram field therefore returns that
restriction comparison. The two inclusion proofs agree by the equality
`g ≫ f = gf`, and proof irrelevance identifies their presentations. -/
theorem transportDataOfComposite_diagram
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).d =
      schemeComparisonFromRestrictions g (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (gf ⁻¹ᵁ U) (gf ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hgf])
        (by rw [← Scheme.Hom.comp_preimage, hgf]) := by
  unfold transportDataOfComposite
  rfl

/-- The first transport is the named restricted-composite comparison,
whiskered through the inverse open-site equivalence. -/
theorem transportDataOfComposite_kappaU
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).κU =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (perfectOverlapCompositeLocalIso f g gf hgf U)
          (overlapSiteInverse (gf ⁻¹ᵁ U)).mapDerivedCategory := by
  rfl

/-- At the first local object, the transport component is the inverse-site
image of the named restricted-composite comparison. -/
theorem transportDataOfComposite_kappaU_hom_app
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    ((transportDataOfComposite f g gf hgf U V A B E φU φV).κU.app A).hom =
      (overlapSiteInverse (gf ⁻¹ᵁ U)).mapDerivedCategory.map
        ((perfectOverlapCompositeLocalIso f g gf hgf U).hom.app A) := by
  have h := congrArg (fun z => z.hom.app A)
    (transportDataOfComposite_kappaU f g gf hgf U V A B E φU φV)
  exact h.trans (associator_symm_whiskerRight_hom_app
    (derivedPullback (f ∣_ U))
    (derivedPullback (g.resLE (f ⁻¹ᵁ U) (gf ⁻¹ᵁ U)
      (by rw [← Scheme.Hom.comp_preimage, hgf])))
    (overlapSiteInverse (gf ⁻¹ᵁ U)).mapDerivedCategory
    (derivedPullback (gf ∣_ U))
    (perfectOverlapCompositeLocalIso f g gf hgf U) A)

/-- The first site field is the fixed return comparison for the inverse-image open.
This follows by projecting the first site component of the composite transport
construction; no choice of restriction diagram affects the component. -/
theorem transportDataOfComposite_siteU
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).siteU =
      openSiteReturnIso X (gf ⁻¹ᵁ U) := by
  rfl

/-- The second site field is the fixed return comparison for its inverse-image open.
Projecting the second site component of the composite transport gives this equation. -/
theorem transportDataOfComposite_siteV
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).siteV =
      openSiteReturnIso X (gf ⁻¹ᵁ V) := by
  rfl

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
  [∀ (Z : Scheme.{u}) (U : Z.Opens),
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))] in
/-- Restricting the two-step map to an open gives the restriction of its
composite. This is the geometric equation used to define the transport
isomorphism and the corresponding open-pullback cube. -/
theorem perfectOverlapRestrictedComposite
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (W : Y₀.Opens) :
    let hP : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP ≫ (f ∣_ W) = gf ∣_ W := by
  intro hP
  apply (cancel_mono W.ι).1
  simp only [Category.assoc, morphismRestrict_ι]
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]



end

end AlgebraicGeometry

