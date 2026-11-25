/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalSupportTower
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-!
# Etale horizontal compact-support exchange is the composition mate

Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7K
(blueprint: lem-pur-etale-horizontal-support-mate).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The compactification-independent proper-support comparison for an etale map.
Source: literature/stacks-project/more-etale.tex, Tags 0F4L and 0GKM
(blueprint: lem-pur-etale-horizontal-support-mate). -/
noncomputable def etaleCanonicalCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e]
    [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian V] [CompactSpace V]
    [QuasiCompact e] [HasCompactification e]
    (N : EtaleCompactSupportNormalization A) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    N.comparison e (HasCompactification.compactification e)

/-- The specified composition mate built from the normalized compact-support comparisons.
Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7K
(blueprint: lem-pur-etale-horizontal-support-mate). -/
noncomputable def etaleHorizontalSupportMateDelta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X']
    [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsLocallyNoetherian Y'] [CompactSpace Y']
    [HasCompactification f] [HasCompactification f']
    [Etale v] [Etale v'] [IsSeparated v] [IsSeparated v']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [HasCompactification v] [HasCompactification v']
    [HasCompactification (v' ≫ f)] [HasCompactification (f' ≫ v)]
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [QuasiCompact (v' ≫ f)] [QuasiCompact (f' ≫ v)]
    (sq : IsPullback v' f' f v)
    (N : EtaleCompactSupportNormalization A) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (etaleCanonicalCompactSupportComparison A v' N).symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
    unboundedEtaleLowerShriekCompIso A v' f ≪≫
    unboundedEtaleLowerShriekCongr A sq.toCommSq.w ≪≫
    (unboundedEtaleLowerShriekCompIso A f' v).symm ≪≫
    Functor.isoWhiskerLeft
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f')
      (etaleCanonicalCompactSupportComparison A v N)

/-- The specified unbounded compact-support exchange `C_{f,v} : v^* Rf_! ≅ Rf'_! v'^*` as an
isomorphism; its `hom` is the recorded exchange and its `inv` is `C_{f,v}⁻¹`.
Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7L
(blueprint: lem-pur-etale-horizontal-support-mate). -/
noncomputable def etaleHorizontalSupportBaseChangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' := by
  haveI : IsIso (unboundedEtaleCompactSupportBaseChange A sq) :=
    (unboundedEtaleCompactSupport_baseChange A sq).1
  exact asIso (unboundedEtaleCompactSupportBaseChange A sq)

attribute [local irreducible] canonicalEtaleCompactSupportComparison

private lemma mono_compactification_to_star_aux
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (F : Sheaf U.smallEtaleTopology B)
    [Mono ((openImmersionLowerShriekToLowerStar B c.i).app F)] :
    Mono ((lowerStar B c.g).map ((openImmersionLowerShriekToLowerStar B c.i).app F) ≫
      (lowerStarComp B c.i c.g f c.comm).hom.app F) := by
  infer_instance

-- The normalization equations force the explicit graph comparison. This reduces the
-- geometric tower calculation to the constructed graph maps, independently of N.
private lemma normalization_comparison_eq_canonical
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] [QuasiCompact f]
    [IsNoetherian U] [IsNoetherian X] (c : Compactification f) :
    N.comparison f c = canonicalEtaleCompactSupportComparison A f c := by
  have hm (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      Mono ((compactificationSheafToDirectImage A c).app F) := by
    have ho (V : c.Z.Etaleᵒᵖ) :
        Mono (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F
          ).hom.app V) :=
      ConcreteCategory.mono_of_injective _
        (openExtensionProperSupport_range A c.i F V.unop).1
    have : Mono
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F).hom :=
      NatTrans.mono_of_mono_app _
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app F) :=
      Sheaf.Hom.mono_of_presheaf_mono c.Z.smallEtaleTopology (ModuleCat.{u + 1} A) _
    exact mono_compactification_to_star_aux (ModuleCat.{u + 1} A) c F
  let core := canonicalEtaleCompactSupportCore A
  have hs : N.sheafComparison f c = core.sheafComparison f c := by
    apply NatTrans.ext
    funext F
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    rw [N.sheaf_normalization, core.sheaf_normalization]
  change N.comparison f c = core.comparison f c
  apply Iso.ext_inv
  apply (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh |>.map_injective
  apply NatTrans.ext
  funext K
  change (N.comparison f c).inv.app (DerivedCategory.Qh.obj K) =
    (core.comparison f c).inv.app (DerivedCategory.Qh.obj K)
  rw [N.derived_normalization, core.derived_normalization, hs]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

private lemma isIso_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    {L₁' : A ⥤ B} {R₁' : B ⥤ A} {L₂' : C ⥤ D} {R₂' : D ⥤ C}
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (eG : G' ≅ G) (eH : H ≅ H')
    (α : TwoSquare G L₁ L₂ H) (K : B) :
    IsIso ((mateEquiv adj₁' adj₂'
      ((((α.whiskerTop eG.hom).whiskerBottom eH.hom).whiskerRight e₂.inv).whiskerLeft
        e₁.hom)).app K) ↔ IsIso ((mateEquiv adj₁ adj₂ α).app K) := by
  rw [conjugateEquiv_mateEquiv_vcomp adj₁' adj₁ adj₂',
    mateEquiv_conjugateEquiv_vcomp adj₁ adj₂ adj₂']
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    isIso_comp_left_iff, isIso_comp_right_iff]
  rw [mate_whiskerBottom, mate_whiskerTop]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_derived_exchange_iff_exact
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) ↔
      IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) := by
  let A := ModuleCat.{u + 1} Λ
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso A sq).hom
  have h := isIso_mate_transport
    (mapDerivedUpperStarLowerStarAdjunction A f)
    (mapDerivedUpperStarLowerStarAdjunction A f')
    (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f')
    (leftDerivedUpperStarIsoMapDerivedCategory A f).symm
    (leftDerivedUpperStarIsoMapDerivedCategory A f').symm
    (leftDerivedUpperStarIsoMapDerivedCategory A g)
    (leftDerivedUpperStarIsoMapDerivedCategory A g').symm α K
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory A g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory A g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory A f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar A g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  rw [hs] at h
  exact h

private theorem open_base_change_mate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [Etale v] [Etale b]
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq v j' j b) :
    openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')).symm
        (TwoSquare.mk _ _ _ _
          (squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).hom)) := by
  let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
  let va := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v
  let ba := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b
  let tau := TwoSquare.mk _ _ _ _ (squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).hom
  let beta := (mateEquiv ja j'a).symm tau
  change (conjugateEquiv (ja.comp ba) (va.comp j'a)).symm
    (mateEquiv ba va tau) = beta
  apply (conjugateEquiv (ja.comp ba) (va.comp j'a)).injective
  rw [Equiv.apply_symm_apply]
  have hi := iterated_mateEquiv_conjugateEquiv ja j'a va ba beta
  rw [Equiv.apply_symm_apply] at hi
  exact hi

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem derived_open_base_change_mate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [Etale v] [Etale b] [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j b) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq).hom =
      ((mateEquiv
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')).symm
        (TwoSquare.mk _ _ _ _
          (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom)
        ) := by
  let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
  let beta := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq)
  let tau := squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip
  have hm := open_base_change_mate A sq.toCommSq
  change beta.hom = ((mateEquiv ja j'a).symm (.mk _ _ _ _ tau.hom)) at hm
  have hu (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      j'a.unit.app _ ≫ (upperStar (ModuleCat.{u + 1} A) j').map (beta.hom.app K) =
        (upperStar (ModuleCat.{u + 1} A) v).map (ja.unit.app K) ≫
          tau.hom.app _ := by
    rw [hm]
    exact (unit_mateEquiv_symm ja j'a (.mk _ _ _ _ tau.hom) K).symm
  have hd (K : DerivedCategoryModule A U) :=
    Adjunction.mapDerivedCategoryAdjunction_mate ja j'a tau beta hu K
  let betad := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} A) sq).hom
  let taud := (exactDerivedSquareUpperStarIso
    (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom
  change betad = ((mateEquiv ja.mapDerivedCategoryAdjunction
    j'a.mapDerivedCategoryAdjunction).symm (.mk _ _ _ _ taud))
  ext K
  apply (j'a.mapDerivedCategoryAdjunction.homEquiv _ _).injective
  rw [j'a.mapDerivedCategoryAdjunction.homEquiv_unit]
  exact (hd K).trans
    (unit_mateEquiv_symm ja.mapDerivedCategoryAdjunction
      j'a.mapDerivedCategoryAdjunction (.mk _ _ _ _ taud) K)

attribute [local irreducible] derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction

-- The nested derived adjunctions require deeper definitional equality checks.
set_option maxRecDepth 10000 in
private theorem derived_open_square_mate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [Etale v] [Etale b] [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j b) :
    let va := derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v inferInstance
    let ba := derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) b inferInstance
    let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j
    let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j'
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
    a.hom = ((mateEquiv va ba).symm
      (.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).hom)) := by
  dsimp only
  let va := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) v inferInstance
  let ba := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) b inferInstance
  let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j
  let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j'
  let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
  rw [derived_open_base_change_mate A sq]
  apply (mateEquiv va ba).injective
  rw [Equiv.apply_symm_apply]
  apply (mateEquiv ja j'a).injective
  rw [Equiv.apply_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  have hi := iterated_mateEquiv_conjugateEquiv va ba j'a ja
    (TwoSquare.mk _ _ _ _ a.hom)
  have hi' := congr_app hi M
  exact hi'.trans (congrArg (fun t => t.app M)
    ((conjugateEquiv (va.comp ja) (j'a.comp ba)).apply_symm_apply
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        sq.toCommSq.flip).hom))

private theorem interchange_mate
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {B : C ⥤ D} {R : D ⥤ C} {L : E ⥤ F} {S : F ⥤ E}
    (b : B ⊣ R) (l : L ⊣ S)
    (P : D ⥤ F) (Q : C ⥤ E)
    (ex : P ⋙ S ⟶ R ⋙ Q) (gam : Q ⋙ L ⟶ B ⋙ P)
    (H : C) (K : D) (beta : H ≅ R.obj K)
    (hg : l.homEquiv _ _ (gam.app H) ≫ ex.app (B.obj H) =
      Q.map (b.unit.app H)) :
    l.homEquiv _ _ (gam.app H ≫ P.map (B.map beta.hom ≫ b.counit.app K)) ≫
      ex.app K ≫ Q.map beta.inv = 𝟙 (Q.obj H) := by
  have hb : b.unit.app H ≫ R.map (B.map beta.hom ≫ b.counit.app K) = beta.hom := by
    rw [R.map_comp, ← Functor.comp_map, ← b.unit.naturality_assoc]
    simp [b.right_triangle_components]
  have hn := ex.naturality (B.map beta.hom ≫ b.counit.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [l.homEquiv_naturality_right, Category.assoc, ← Category.assoc
    (S.map (P.map _)), hn, ← Category.assoc, ← Category.assoc, hg]
  rw [← Q.map_comp, hb, ← Q.map_comp]
  simp

private theorem mate_transport
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {S : D ⥤ C} (l : L ⊣ S)
    {H H' : C} {K K' : D} (s : H' ≅ H) (t : K ≅ K')
    (g : L.obj H ⟶ K) (e : S.obj K ⟶ H)
    (h : l.homEquiv _ _ g ≫ e = 𝟙 H) :
    l.homEquiv _ _ (L.map s.hom ≫ g ≫ t.hom) ≫
      S.map t.inv ≫ e ≫ s.inv = 𝟙 H' := by
  rw [l.homEquiv_naturality_left, l.homEquiv_naturality_right]
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, t.hom_inv_id, S.map_id, Category.id_comp]
  rw [← Category.assoc (l.homEquiv _ _ g), h]
  simp

-- Rotate the inverse of an invertible square across the other two adjunctions.
-- This separates the geometric sum-exchange normalization from proper base change.
private lemma rotated_inverse_mate
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {T : F ⥤ D} {P : D ⥤ F} {U : E ⥤ C} {Q : C ⥤ E}
    {L : E ⥤ F} {S : F ⥤ E} {B : C ⥤ D} {R : D ⥤ C}
    (t : T ⊣ P) (u : U ⊣ Q) (l : L ⊣ S) (b : B ⊣ R)
    (beta : U ⋙ B ≅ L ⋙ T) (ex : P ⋙ S ≅ R ⋙ Q)
    (h : conjugateEquiv (l.comp t) (u.comp b) beta.hom = ex.hom) :
    (mateEquiv u t (.mk _ _ _ _ beta.inv)) =
      ((mateEquiv b l).symm (.mk _ _ _ _ ex.inv)) := by
  have he : conjugateIsoEquiv (l.comp t) (u.comp b) beta = ex := Iso.ext h
  have hi : conjugateEquiv (u.comp b) (l.comp t) beta.inv = ex.inv :=
    congrArg Iso.inv he
  apply (mateEquiv b l).injective
  rw [Equiv.apply_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  exact congr_app ((iterated_mateEquiv_conjugateEquiv u t l b
    (.mk _ _ _ _ beta.inv)).trans hi) M

attribute [local irreducible] rightDerivedLowerShriekIso
  unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr
  mapDerivedUpperStarLowerStarAdjunction

-- Keep the pullback compactification and its projection definitionally aligned.
set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- The counit identity for the composition mate of compact-support exchange.
Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7K
(blueprint: lem-pur-etale-horizontal-support-mate).

Proof: the sheaf comparison into direct image is monic. The graph and homotopy
normalization equations therefore identify N with the explicit canonical graph
comparison. Expand the inverse composition comparison on the proper/open tower of a
compactification of f. The separate tower lemma identifies this geometric normalization
before either horizontal counit is applied. Conjugacy of iterated mates identifies
its proper/sum factor with the inverse mate of inverse proper exchange. The open
square comparison is an iterated
mate of the inverse-image square; descend the sheaf mate identity for the two open
extensions, and use the actual localized etale adjunctions for the horizontal arrows.
The mate counit identity replaces the open comparison followed by the v' counit with
open base change followed by the pulled-back etale counit. On the proper square, the
unit identity for mates and its triangle identity show that the resulting transpose
is inverse proper exchange. Naturality transports this calculation through the two
model-to-chosen comparisons. The specified compact-support exchange is exactly the
proper exchange followed by inverse open base change in this model. Cancelling that
isomorphism identifies the adjunct with its inverse. Apply the adjunction bijection
backwards to obtain the displayed counit identity on every unbounded input.
-/
theorem etaleHorizontalSupportMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [IsSeparated f'] [IsSeparated v] [IsSeparated v']
    [Etale v] [Etale v'] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification f] [HasCompactification f'] [HasCompactification v]
    [HasCompactification v'] [HasCompactification (v' ≫ f)]
    [HasCompactification (f' ≫ v)] [QuasiCompact (v' ≫ f)]
    [QuasiCompact (f' ≫ v)] (sq : IsPullback v' f' f v)
    (N : EtaleCompactSupportNormalization A) :
    ∀ (M : DerivedCategoryModule A X),
      (etaleHorizontalSupportMateDelta A sq N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory.obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v'
            inferInstance).counit.app M) =
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((etaleHorizontalSupportBaseChangeIso A sq).inv.app M) ≫
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
        inferInstance).counit.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) := by
  intro M
  let B₀ := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  let cs := c.ofIsPullback sq
  let psq := IsPullback.of_hasPullback c.g v
  let jsq := c.isPullback_i_ofIsPullback sq
  let J := (openImmersionLowerShriek B₀ c.i).mapDerivedCategory
  let J' := (openImmersionLowerShriek B₀ cs.i).mapDerivedCategory
  let V := (upperStar B₀ v').mapDerivedCategory
  let B := (etaleLowerShriek B₀ (pullback.fst c.g v) inferInstance).mapDerivedCategory
  let R := (upperStar B₀ (pullback.fst c.g v)).mapDerivedCategory
  let L := (etaleLowerShriek B₀ v inferInstance).mapDerivedCategory
  let S := (upperStar B₀ v).mapDerivedCategory
  let P := rightDerivedLowerStar B₀ c.g
  let Q := rightDerivedLowerStar B₀ cs.g
  let b := derivedEtaleLowerShriekUpperStarAdjunction B₀ (pullback.fst c.g v)
    inferInstance
  let l := derivedEtaleLowerShriekUpperStarAdjunction B₀ v inferInstance
  let va := derivedEtaleLowerShriekUpperStarAdjunction B₀ v' inferInstance
  let t := rightDerivedLowerShriekIso A c
  let t' := rightDerivedLowerShriekIso A cs
  let beta := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B₀ jsq).app M
  let ex := exactDerivedBaseChangeMap B₀ psq.toCommSq
  have : IsIso (derivedBaseChangeMap B₀ psq.toCommSq) :=
    isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
      isAddTorsion_of_finite psq
  have : IsIso ex := by
    have (K : DerivedCategoryModule A c.Z) : IsIso (ex.app K) :=
      (isIso_derived_exchange_iff_exact A psq.toCommSq K).mp inferInstance
    exact NatIso.isIso_of_isIso_app ex
  let gam := ((mateEquiv b l).symm (.mk _ _ _ _ (inv ex)))
  let pa := mapDerivedUpperStarLowerStarAdjunction B₀ c.g
  let qa := mapDerivedUpperStarLowerStarAdjunction B₀ cs.g
  let tau := exactDerivedSquareUpperStarIso B₀ psq.toCommSq
  let sumEx := ((mateEquiv l b).symm (.mk _ _ _ _ tau.hom))
  have hconj : conjugateEquiv (l.comp pa) (qa.comp b) sumEx = ex := by
    have h := iterated_mateEquiv_conjugateEquiv l b qa pa
      ((mateEquiv l b).symm (.mk _ _ _ _ tau.hom))
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have : IsIso (conjugateEquiv (l.comp pa) (qa.comp b) sumEx) := by
    rw [hconj]
    infer_instance
  have : IsIso sumEx := conjugateEquiv_of_iso (l.comp pa) (qa.comp b) sumEx
  let gam' := (mateEquiv qa pa (.mk _ _ _ _ (inv sumEx)))
  have hgam : gam' = gam :=
    rotated_inverse_mate pa qa l b (asIso sumEx) (asIso ex) hconj
  let H := J'.obj (V.obj M)
  let K := J.obj M
  have hg : l.homEquiv _ _ (gam.app H) ≫ ex.app (B.obj H) =
      Q.map (b.unit.app H) := by
    rw [Adjunction.homEquiv_unit]
    have hu := unit_mateEquiv_symm b l (.mk _ _ _ _ (inv ex)) H
    change Q.map (b.unit.app H) ≫ (inv ex).app (B.obj H) =
      l.unit.app (Q.obj H) ≫ S.map (gam.app H) at hu
    change (l.unit.app (Q.obj H) ≫ S.map (gam.app H)) ≫ ex.app (B.obj H) = _
    rw [← hu, Category.assoc]
    simp
  have hm := interchange_mate b l P Q ex gam H K beta hg
  let aiso := (conjugateIsoEquiv
      (va.comp (derivedOpenImmersionLowerShriekUpperStarAdjunction B₀ c.i))
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction B₀ cs.i).comp b)).symm
    (exactDerivedSquareUpperStarIso B₀ jsq.toCommSq.flip)
  let a := aiso.hom
  have ha : a.app (V.obj M) ≫ J.map (va.counit.app M) =
      B.map beta.hom ≫ b.counit.app K := by
    have h := derived_open_square_mate A jsq
    change a = ((mateEquiv va b).symm
      (.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B₀ jsq).hom)
        ) at h
    rw [h]
    exact (mateEquiv_counit_symm va b
      (.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B₀ jsq).hom)
      M).symm
  have hraw := etaleHorizontalSupport_tower A sq c (V.obj M)
  rw [← normalization_comparison_eq_canonical A N v'
    (HasCompactification.compactification v'),
    ← normalization_comparison_eq_canonical A N v
      (HasCompactification.compactification v)] at hraw
  change (etaleHorizontalSupportMateDelta A sq N).inv.app (V.obj M) =
    L.map (t'.inv.app (V.obj M)) ≫ gam'.app H ≫
      P.map (a.app (V.obj M)) ≫ t.hom.app _ at hraw
  rw [hgam] at hraw
  have ht : (etaleHorizontalSupportMateDelta A sq N).inv.app (V.obj M) ≫
      (rightDerivedLowerShriek B₀ f).map (va.counit.app M) =
    L.map (t'.inv.app (V.obj M)) ≫ gam.app H ≫
      P.map (B.map beta.hom ≫ b.counit.app K) ≫ t.hom.app M := by
    rw [hraw]
    simp only [Category.assoc]
    erw [← t.hom.naturality (va.counit.app M)]
    change L.map (t'.inv.app (V.obj M)) ≫ gam.app H ≫ P.map (a.app (V.obj M)) ≫
      P.map (J.map (va.counit.app M)) ≫ t.hom.app M = _
    rw [← P.map_comp_assoc, ha]
  have hc := congr_app ((unboundedEtaleCompactSupport_baseChange A sq).2 c) M
  rw [unboundedEtaleCompactSupport_exchange_normalization A sq c] at hc
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at hc
  change (etaleHorizontalSupportBaseChangeIso A sq).hom.app M =
    S.map (t.inv.app M) ≫ ex.app K ≫ Q.map beta.inv ≫ t'.hom.app (V.obj M) at hc
  have h : l.homEquiv _ _
      ((etaleHorizontalSupportMateDelta A sq N).inv.app (V.obj M) ≫
        (rightDerivedLowerShriek B₀ f).map (va.counit.app M)) =
      (etaleHorizontalSupportBaseChangeIso A sq).inv.app M := by
    apply (cancel_mono ((etaleHorizontalSupportBaseChangeIso A sq).hom.app M)).1
    rw [Iso.inv_hom_id_app]
    rw [ht, hc]
    simpa only [Category.assoc, Functor.id_obj, Functor.comp_obj,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, L, V] using
      mate_transport l (t'.app (V.obj M)).symm (t.app M)
        (gam.app H ≫ P.map (B.map beta.hom ≫ b.counit.app K))
        (ex.app K ≫ Q.map beta.inv) hm
  exact ((l.homEquiv _ _).symm_apply_apply _).symm.trans
    (congrArg ((l.homEquiv _ _).symm) h)

end AlgebraicGeometry.Etale
