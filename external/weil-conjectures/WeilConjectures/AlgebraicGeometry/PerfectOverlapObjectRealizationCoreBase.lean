/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
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

private theorem cancel_iso_pasting {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (s : D ≅ B)
    (g : D ⟶ E) (h : E ⟶ D) (gh : g ≫ h = 𝟙 D) :
    f = 𝟙 A ≫ f ≫ s.inv ≫ g ≫ 𝟙 E ≫ h ≫ s.hom := by
  simp only [Category.id_comp, Category.comp_id,
    ← Category.assoc, gh, Category.comp_id, Iso.inv_hom_id]

/-- The fixed pullback from a finite overlap stage to the colimit overlap. -/
noncomputable def perfectOverlapCoreTransition
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (k : Set.Ici i) :
    schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))) ⥤
      schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))) :=
  derivedPullback (baseChangeMap s (overlapLimitArrow R c k))

/-- The fixed composition comparison for the overlap transition. -/
noncomputable def perfectOverlapCoreBaseComparison
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (k : Set.Ici i) :
    derivedPullback (pullback.fst s (Spec.map (c.ι.app i))) ≅
      derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property)))) ⋙
        perfectOverlapCoreTransition R c i Y s k :=
  perfectHomComparison s (overlapLimitArrow R c k)

/-- The fixed overlap comparison is the composition comparison for the
canonical arrow from the colimit to the finite stage. -/
theorem perfectOverlapCoreBaseComparison_eq
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (k : Set.Ici i) :
    perfectOverlapCoreBaseComparison R c i Y s k =
      perfectHomComparison s (overlapLimitArrow R c k) := rfl

/-- Natural derived-pullback comparison for two cartesian identifications.
Source: Stacks Project, Tag 0D5S. The two sides are pullbacks along the same
scheme map after `h`. Compose the fixed pullback-composition isomorphism for
`e.inv` and `r`, transport across `h`, and invert the fixed comparison for
`m` and `d.inv`. Naturality follows from that of each factor. -/
noncomputable def perfectOverlapDerivedPullbackTransport
    {Y Z A B : Scheme.{u}}
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (r : Y ⟶ Z) (e : Y ≅ A) (d : Z ≅ B) (m : A ⟶ B)
    (h : e.inv ≫ r = m ≫ d.inv) :
    derivedPullback r ⋙ derivedPullback e.inv ≅
      derivedPullback d.inv ⋙ derivedPullback m :=
  perfectHomComposition e.inv r ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) h) ≪≫
      (perfectHomComposition m d.inv).symm

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- The derived equivalence between the localized module site and its open scheme. -/
@[no_expose] noncomputable def perfectOverlapOpenSiteDerivedEquiv
    (X : Scheme.{u}) (W : X.Opens)
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over W))] :
    DerivedCategory (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over W)) ≌ schemeDerivedCategory W.toScheme := by
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv W
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  letI : e.inverse.IsEquivalence := e.isEquivalence_inverse
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact e.mapDerivedCategory

/-- The natural comparison after returning from the open site to its scheme.
The site counit removes the inverse/direct equivalence pair. The resulting two
pullback compositions agree by the given geometric square. -/
noncomputable def perfectOverlapNaturalComparisonFromGeometry
    {X Z A B : Scheme.{u}} (W : X.Opens)
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over W))]
    (r : W.toScheme ⟶ Z) (e : W.toScheme ≅ A) (d : Z ≅ B)
    (m : A ⟶ B) (h : e.inv ≫ r = m ≫ d.inv) :
    (derivedPullback r ⋙ (perfectOverlapOpenSiteDerivedEquiv X W).inverse) ⋙
      ((perfectOverlapOpenSiteDerivedEquiv X W).functor ⋙
        derivedPullback e.inv) ≅
      derivedPullback d.inv ⋙ derivedPullback m := by
  let site := perfectOverlapOpenSiteDerivedEquiv X W
  let cancel := site.counitIso
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (derivedPullback r)
      (Functor.isoWhiskerRight cancel (derivedPullback e.inv)) ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.leftUnitor _) ≪≫
    perfectOverlapDerivedPullbackTransport r e d m h

/-- The component equation for the cartesian overlap comparison.
The two maps into the later open subscheme agree after its open immersion: the
first projection follows from the restricted-map equations and the pullback
first projections, and the second from the base-change square and pullback
second projections. The later cartesian square then identifies the maps. -/
theorem perfectOverlapCartesianComponent
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (a : C ⟶ T) (q : T ⟶ S)
    (hgf : gk ≫ f = g) (hgk : gk ≫ pK = pX ≫ a)
    (hf : IsPullback f pK pY q) (W : Y.Opens)
    (r : (g ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ W).toScheme)
    (hr : r ≫ (f ⁻¹ᵁ W).ι = (g ⁻¹ᵁ W).ι ≫ gk)
    (eY : (g ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) (a ≫ q))
    (eK : (f ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) q)
    (hYfst : eY.inv ≫ (g ∣_ W) = pullback.fst (W.ι ≫ pY) (a ≫ q))
    (hYsnd : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX =
      pullback.snd (W.ι ≫ pY) (a ≫ q))
    (hKfst : eK.inv ≫ (f ∣_ W) = pullback.fst (W.ι ≫ pY) q)
    (hKsnd : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK = pullback.snd (W.ι ≫ pY) q) :
    eY.inv ≫ r =
      baseChangeMap (W.ι ≫ pY)
        (Over.homMk a (by rfl) : Over.mk (a ≫ q) ⟶ Over.mk q) ≫ eK.inv := by
  let m := baseChangeMap (W.ι ≫ pY)
    (Over.homMk a (by rfl) : Over.mk (a ≫ q) ⟶ Over.mk q)
  have hrf : r ≫ (f ⁻¹ᵁ W).ι ≫ f = (g ⁻¹ᵁ W).ι ≫ g := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι f, hr, Category.assoc, hgf]
  have hrpK : r ≫ (f ⁻¹ᵁ W).ι ≫ pK = (g ⁻¹ᵁ W).ι ≫ pX ≫ a := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι pK, hr, Category.assoc, hgk]
  have hYtoY : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g =
      pullback.fst (W.ι ≫ pY) (a ≫ q) ≫ W.ι := by
    calc
      eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g = eY.inv ≫ (g ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eY.inv ≫ z) (morphismRestrict_ι g W).symm
      _ = pullback.fst (W.ι ≫ pY) (a ≫ q) ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hYfst
  have hKtoY : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f =
      pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
    calc
      eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f = eK.inv ≫ (f ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eK.inv ≫ z) (morphismRestrict_ι f W).symm
      _ = pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hKfst
  have hmfst : m ≫ pullback.fst (W.ι ≫ pY) q =
      pullback.fst (W.ι ≫ pY) (a ≫ q) := by
    exact baseChangeMap_fst _ _
  have hmsnd : m ≫ pullback.snd (W.ι ≫ pY) q =
      pullback.snd (W.ι ≫ pY) (a ≫ q) ≫ a := by
    exact baseChangeMap_snd _ _
  apply (cancel_mono (f ⁻¹ᵁ W).ι).1
  apply hf.hom_ext
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ f =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrf
      _ = pullback.fst (W.ι ≫ pY) (a ≫ q) ≫ W.ι := hYtoY
      _ = m ≫ pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ W.ι) hmfst.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKtoY.symm
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ pK =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX ≫ a := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrpK
      _ = pullback.snd (W.ι ≫ pY) (a ≫ q) ≫ a := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ a) hYsnd
      _ = m ≫ pullback.snd (W.ι ≫ pY) q := by
        exact hmsnd.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKsnd.symm

/-- The component equation for the cartesian overlap comparison.
The two maps into the later open subscheme agree after its open immersion: the
first projection follows from the restricted-map equations and the pullback
first projections, and the second from the base-change square and pullback
second projections. The later cartesian square then identifies the maps. -/
theorem perfectOverlapCartesianComponentOver
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (l : Over.mk b ⟶ Over.mk q)
    (hgf : gk ≫ f = g) (hgk : gk ≫ pK = pX ≫ l.left)
    (hf : IsPullback f pK pY q) (W : Y.Opens)
    (r : (g ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ W).toScheme)
    (hr : r ≫ (f ⁻¹ᵁ W).ι = (g ⁻¹ᵁ W).ι ≫ gk)
    (eY : (g ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) b)
    (eK : (f ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) q)
    (hYfst : eY.inv ≫ (g ∣_ W) = pullback.fst (W.ι ≫ pY) b)
    (hYsnd : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX =
      pullback.snd (W.ι ≫ pY) b)
    (hKfst : eK.inv ≫ (f ∣_ W) = pullback.fst (W.ι ≫ pY) q)
    (hKsnd : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK = pullback.snd (W.ι ≫ pY) q) :
    eY.inv ≫ r =
      baseChangeMap (W.ι ≫ pY)
        l ≫ eK.inv := by
  let m := baseChangeMap (W.ι ≫ pY)
    l
  have hrf : r ≫ (f ⁻¹ᵁ W).ι ≫ f = (g ⁻¹ᵁ W).ι ≫ g := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι f, hr, Category.assoc, hgf]
  have hrpK : r ≫ (f ⁻¹ᵁ W).ι ≫ pK = (g ⁻¹ᵁ W).ι ≫ pX ≫ l.left := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι pK, hr, Category.assoc, hgk]
  have hYtoY : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g =
      pullback.fst (W.ι ≫ pY) b ≫ W.ι := by
    calc
      eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g = eY.inv ≫ (g ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eY.inv ≫ z) (morphismRestrict_ι g W).symm
      _ = pullback.fst (W.ι ≫ pY) b ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hYfst
  have hKtoY : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f =
      pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
    calc
      eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f = eK.inv ≫ (f ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eK.inv ≫ z) (morphismRestrict_ι f W).symm
      _ = pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hKfst
  have hmfst : m ≫ pullback.fst (W.ι ≫ pY) q =
      pullback.fst (W.ι ≫ pY) b := by
    exact baseChangeMap_fst _ _
  have hmsnd : m ≫ pullback.snd (W.ι ≫ pY) q =
      pullback.snd (W.ι ≫ pY) b ≫ l.left := by
    exact baseChangeMap_snd _ _
  apply (cancel_mono (f ⁻¹ᵁ W).ι).1
  apply hf.hom_ext
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ f =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrf
      _ = pullback.fst (W.ι ≫ pY) b ≫ W.ι := hYtoY
      _ = m ≫ pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ W.ι) hmfst.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKtoY.symm
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ pK =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX ≫ l.left := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrpK
      _ = pullback.snd (W.ι ≫ pY) b ≫ l.left := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ l.left) hYsnd
      _ = m ≫ pullback.snd (W.ι ≫ pY) q := by
        exact hmsnd.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKsnd.symm

/-- The two canonical overlap object comparisons packaged without expanding
the stagewise transport record. The branch equations are exactly the
comparison, transported local identification, and site restriction maps. -/
noncomputable def perfectOverlapPsiFromDiagram
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV)
    (A' : A) (B' : B) (E : D)
    (θU : d.HU.obj A' ≅ RU.obj E)
    (θV : d.HV.obj B' ≅ RV.obj E)
    (b : Bool) :
    d.HW.obj (if b then SV.obj B' else SU.obj A') ≅ RW.obj E :=
  match b with
  | false => d.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
  | true => d.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E

/-- The first component of the canonical overlap object comparison.
Source: Stacks Project, Tags 08DW and 0D5S. On the first open, invert the
intersection comparison `γU`, map the transported local identification through
the smaller-open restriction, then use `τU` to identify the two site restrictions.
This is exactly the false branch of the defining comparison. -/
@[simp] theorem perfectOverlapPsiFromDiagram_false
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV)
    (A' : A) (B' : B) (E : D)
    (θU : d.HU.obj A' ≅ RU.obj E)
    (θV : d.HV.obj B' ≅ RV.obj E) :
    perfectOverlapPsiFromDiagram d A' B' E θU θV false =
      d.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E := by
  rfl

/-- The second component of the canonical overlap object comparison.
Source: Stacks Project, Tags 08DW and 0D5S. On the second open, invert the
intersection comparison `γV`, map the transported local identification through
the smaller-open restriction, then use `τV` to identify the two site restrictions.
This is exactly the true branch of the defining comparison. -/
@[simp] theorem perfectOverlapPsiFromDiagram_true
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV)
    (A' : A) (B' : B) (E : D)
    (θU : d.HU.obj A' ≅ RU.obj E)
    (θV : d.HV.obj B' ≅ RV.obj E) :
    perfectOverlapPsiFromDiagram d A' B' E θU θV true =
      d.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E := by
  rfl

/-- Invert the first-open coherence square at a global object.
Source: Stacks Project, Tag 08DW. The defining square says that the path through
`τU⁻¹`, `βU`, and `γU` equals the path through `βW` and `αU⁻¹`.
Compose on the left with `αU` and `βW⁻¹`, then cancel `γU` on the right.
Functoriality and the inverse laws for the natural isomorphisms give the formula. -/
theorem overlapDiagram_gammaU_inv_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV) (F : C) :
    d.γU.inv.app (TU.obj F) =
      d.HW.map (αU.hom.app F) ≫ d.βW.inv.app F ≫
        τU.inv.app (L.obj F) ≫ SP.map (d.βU.hom.app F) := by
  apply (cancel_mono (d.γU.hom.app (TU.obj F))).1
  calc
    d.γU.inv.app (TU.obj F) ≫ d.γU.hom.app (TU.obj F) = 𝟙 _ := by simp
    _ = d.HW.map (αU.hom.app F) ≫ d.βW.inv.app F ≫
          (d.βW.hom.app F ≫ d.HW.map (αU.inv.app F)) := by simp
    _ = (d.HW.map (αU.hom.app F) ≫ d.βW.inv.app F ≫
          τU.inv.app (L.obj F) ≫ SP.map (d.βU.hom.app F)) ≫
          d.γU.hom.app (TU.obj F) := by
      simp only [Category.assoc]
      rw [d.coherenceU F]

/-- Invert the second-open coherence square at a global object.
Source: Stacks Project, Tag 08DW. Compose the defining second-open square
with the inverses of `αV`, `βW`, and `γV`. The inverse laws cancel these
isomorphisms and leave the displayed expression for the inverse component. -/
theorem overlapDiagram_gammaV_inv_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV) (F : C) :
    d.γV.inv.app (TV.obj F) =
      d.HW.map (αV.hom.app F) ≫ d.βW.inv.app F ≫
        τV.inv.app (L.obj F) ≫ SQ.map (d.βV.hom.app F) := by
  apply (cancel_mono (d.γV.hom.app (TV.obj F))).1
  calc
    d.γV.inv.app (TV.obj F) ≫ d.γV.hom.app (TV.obj F) = 𝟙 _ := by simp
    _ = d.HW.map (αV.hom.app F) ≫ d.βW.inv.app F ≫
          (d.βW.hom.app F ≫ d.HW.map (αV.inv.app F)) := by simp
    _ = (d.HW.map (αV.hom.app F) ≫ d.βW.inv.app F ≫
          τV.inv.app (L.obj F) ≫ SQ.map (d.βV.hom.app F)) ≫
          d.γV.hom.app (TV.obj F) := by
      simp only [Category.assoc]
      rw [d.coherenceV F]



/-- Geometric object comparisons and their natural compatibility with apex pullback.
The transition functors and their fixed conjugation formula are recorded explicitly;
the Hom pin will be derived from naturality, rather than included as a field.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data). -/
structure PerfectHomObjectRealizationCore
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i)) (objects : Bool → schemeDerivedCategory Y)
    (stageEquiv : ∀ k : Set.Ici i, C k ≌
      schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))))
    (apexEquiv : D ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    where
  stageObj : ∀ k b, (stageEquiv k).functor.obj (F k b) ≅
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
      (objects b)
  apexObj : ∀ b, apexEquiv.functor.obj (O b) ≅
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj (objects b)

  transition : ∀ k : Set.Ici i,
    schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))) ⥤
      schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))
  baseComparison : ∀ k : Set.Ici i,
    derivedPullback (pullback.fst s (Spec.map (c.ι.app i))) ≅
      derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property)))) ⋙ transition k
  transition_pin : ∀ (k : Set.Ici i) (P Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj Q),
    perfectLimitMap R c s k.property f =
      (baseComparison k).hom.app P ≫ (transition k).map f ≫ (baseComparison k).inv.app Q
  comparison : ∀ k : Set.Ici i,
    G k ⋙ apexEquiv.functor ≅ (stageEquiv k).functor ⋙ transition k
  object_pin : ∀ (k : Set.Ici i) (b : Bool),
    apexEquiv.functor.map (ψ k b).hom ≫ (apexObj b).hom ≫
      (baseComparison k).hom.app (objects b) =
        (comparison k).hom.app (F k b) ≫ (transition k).map (stageObj k b).hom

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- The object-comparison proposition for the fixed overlap scheme and pullback objects.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data). -/
@[irreducible] noncomputable def perfectOverlapObjectRealizationCoreStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    Nonempty (
      Σ data : (k : I) → (hjk : j ≤ k) →
        perfectOverlapComparisonDataType R c hc i Z t j hij (fun _ _ ↦ ⟨j, le_rfl⟩)
          U V hcover hU hV A B hA hB E φU φV k hjk,
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A) stageEquiv apexEquiv)

end AlgebraicGeometry

