/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonSquareProEtalePathNormalizationSupplement
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonSquareSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # The proper site-comparison factor

Source: Stacks Project, Tags 09A6, 09AF and 099R; the factor calculation in
lem-amb-compact-support-site-comparison-open
(blueprint: lem-amb-compact-support-proper-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem cube
    {A B C D P Q R S : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category P] [Category Q] [Category R] [Category S]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : P ⥤ Q} {R₃ : Q ⥤ P} {L₄ : R ⥤ S} {R₄ : S ⥤ R}
    (ad₁ : L₁ ⊣ R₁) (ad₂ : L₂ ⊣ R₂) (ad₃ : L₃ ⊣ R₃) (ad₄ : L₄ ⊣ R₄)
    {G : A ⥤ C} {H : B ⥤ D} {G' : P ⥤ R} {H' : Q ⥤ S}
    {N₁ : A ⥤ P} {N₂ : B ⥤ Q} {N₃ : C ⥤ R} {N₄ : D ⥤ S}
    (s : L₁ ⋙ N₂ ≅ N₁ ⋙ L₃) (t : L₂ ⋙ N₄ ≅ N₃ ⋙ L₄)
    (a : G ⋙ N₃ ≅ N₁ ⋙ G') (h : H ⋙ N₄ ≅ N₂ ⋙ H')
    (e : G ⋙ L₂ ⟶ L₁ ⋙ H) (p : G' ⋙ L₄ ⟶ L₃ ⋙ H')
    (b : R₁ ⋙ N₁ ⟶ N₂ ⋙ R₃) (b' : R₂ ⋙ N₃ ⟶ N₄ ⋙ R₄)
    (hb : ∀ K, s.hom.app (R₁.obj K) ≫ L₃.map (b.app K) ≫
      ad₃.counit.app (N₂.obj K) = N₂.map (ad₁.counit.app K))
    (hb' : ∀ K, t.hom.app (R₂.obj K) ≫ L₄.map (b'.app K) ≫
      ad₄.counit.app (N₄.obj K) = N₄.map (ad₂.counit.app K))
    (hc : ∀ M, N₄.map (e.app M) ≫ h.hom.app (L₁.obj M) ≫
      H'.map (s.hom.app M) = t.hom.app (G.obj M) ≫
        L₄.map (a.hom.app M) ≫ p.app (N₁.obj M)) (K : B) :
    G'.map (b.app K) ≫ (mateEquiv ad₃ ad₄ (TwoSquare.mk _ _ _ _ p)).app (N₂.obj K) ≫
      R₄.map (h.inv.app K) =
    a.inv.app (R₁.obj K) ≫ N₃.map ((mateEquiv ad₁ ad₂ (TwoSquare.mk _ _ _ _ e)).app K) ≫
      b'.app (H.obj K) := by
  apply (ad₄.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hs (M : A) : p.app (N₁.obj M) ≫ H'.map (s.inv.app M) ≫
      h.inv.app (L₁.obj M) =
      L₄.map (a.inv.app M) ≫ t.inv.app (G.obj M) ≫ N₄.map (e.app M) := by
    apply (cancel_epi (t.hom.app (G.obj M) ≫ L₄.map (a.hom.app M))).1
    simp only [Category.assoc]
    rw [← reassoc_of% (hc M)]
    simp only [← H'.map_comp_assoc, ← L₄.map_comp_assoc,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Iso.hom_inv_id_app_assoc]
    rw [Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hb0 : L₃.map (b.app K) ≫ ad₃.counit.app (N₂.obj K) =
      s.inv.app (R₁.obj K) ≫ N₂.map (ad₁.counit.app K) := by
    rw [← hb K, Iso.inv_hom_id_app_assoc]
  have hb1 : L₄.map (b'.app (H.obj K)) ≫ ad₄.counit.app (N₄.obj (H.obj K)) =
      t.inv.app (R₂.obj (H.obj K)) ≫ N₄.map (ad₂.counit.app (H.obj K)) := by
    rw [← hb' (H.obj K), Iso.inv_hom_id_app_assoc]
  have hp := p.naturality (b.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hp
  rw [ad₄.counit_naturality, reassoc_of% (mateEquiv_counit ad₃ ad₄ p (N₂.obj K)),
    reassoc_of% hp, ← H'.map_comp_assoc, hb0, H'.map_comp]
  simp only [Category.assoc]
  have hn := h.inv.naturality (ad₁.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn, reassoc_of% (hs (R₁.obj K))]
  dsimp only [Functor.comp_obj]
  rw [hb1]
  have ht := t.inv.naturality
    ((mateEquiv ad₁ ad₂ (TwoSquare.mk _ _ _ _ e)).app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ht
  rw [reassoc_of% ht]
  have hm := N₄.congr_map
    (mateEquiv_counit ad₁ ad₂ (TwoSquare.mk _ _ _ _ e) K)
  dsimp only [TwoSquare.mk] at hm
  simp only [Functor.map_comp] at hm
  rw [hm]

private theorem inclusion_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl
private theorem inclusion_comp_inv {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).symm.app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K
private theorem edge_exact (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (leftDerivedUpperStarComparisonIso f A).hom.app M =
      DerivedCategory.Plus.ι.map ((fixedComparisonPullbackPlus A f).hom.app M) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M.obj) := by
  simp only [leftDerivedUpperStarComparisonIso, fixedComparisonPullbackPlus,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app,
    Functor.map_comp, inclusion_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  rfl
private theorem plus_square (A : Type (u + 1)) [CommRing A]
    {Z' Z S' S : Scheme.{u}} {h : Z' ⟶ Z} {p' : Z' ⟶ S'}
    {p : Z ⟶ S} {a : S' ⟶ S} (sq : IsPullback p' h a p)
    (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z').mapDerivedCategoryPlus.map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} A) sq.flip.toCommSq).hom.app M) ≫
      (fixedComparisonPullbackPlus A h).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategoryPlus.obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus.map
        ((fixedComparisonPullbackPlus A p).hom.app M) =
    (fixedComparisonPullbackPlus A p').hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus.obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) p').mapDerivedCategoryPlus.map
        ((fixedComparisonPullbackPlus A a).hom.app M) ≫
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (upperStarCompIso (ModuleCat.{u + 1} A) sq.w) ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlus.obj M) := by
  let cs : ChosenCartesianSquare h p' p a :=
    { toCommSq := sq.flip.toCommSq, isoPullback := sq.flip.isoPullback,
      hom_fst := sq.flip.isoPullback_hom_fst, hom_snd := sq.flip.isoPullback_hom_snd }
  apply DerivedCategory.Plus.ι.map_injective
  have hc := comparison_square A sq.flip M
  rw [square_exact A sq.flip.toCommSq cs] at hc
  simp only [edge_exact, Functor.map_comp, Category.assoc] at hc
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).inv.naturality_assoc,
    ← (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p').inv.naturality_assoc,
    ← (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p').inv.naturality_assoc]
      at hc
  simp only [Functor.comp_obj, Functor.comp_map] at hc
  simp only [Iso.inv_hom_id_app_assoc] at hc
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).inv.naturality] at hc
  simp only [Functor.map_comp, inclusion_map, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, inclusion_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Functor.comp_obj]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.comp_obj] at hc ⊢
  have hx := (upperStar (ModuleCat.{u + 1} A) p').mapDerivedCategory.congr_map
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).inv_hom_id_app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj M.obj))
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hx
  rw [reassoc_of% hx] at hc
  apply (cancel_mono
    ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj M.obj)) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).inv.app
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj M.obj)))).1
  convert hc using 1 <;> simp only [Category.assoc]
  all_goals rfl

private theorem etale_mate_eq (A : Type (u + 1)) [CommRing A]
    {Z' Z S' S : Scheme.{u}} {h : Z' ⟶ Z} {p' : Z' ⟶ S'}
    {p : Z ⟶ S} {a : S' ⟶ S} (sq : CommSq h p' p a) :
    (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p)
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p')
      (Etale.pullbackSquareComparison (ModuleCat.{u + 1} A) sq).hom) =
      Etale.baseChange (ModuleCat.{u + 1} A) sq := by
  apply NatTrans.ext
  funext K
  rw [Etale.baseChange_app, Etale.baseChangeUnitStep_app,
    Etale.baseChangeSquareStep_hom_app, Etale.baseChangeCounitStep_app]
  simp only [mateEquiv, Equiv.coe_fn_mk,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_map, Category.id_comp, Functor.comp_obj]
  erw [Category.comp_id]

/-- The proper factor of the compact-support site-comparison square.
Source: Stacks Project, Tags 099R and 0B65; step 4 of
lem-amb-compact-support-site-comparison-open
(blueprint: lem-amb-compact-support-proper-factor).

Proof: the two direct-image comparisons are the counit-normalized mates. Expand
both proper exchanges as mates of the pullback square. Transpose the two paths
under the target pullback/direct-image adjunction. Naturality moves the source
comparison through the counit. The defining counit identity of the comparison
mate cancels it. Composition coherence of the inverse-image comparison identifies
the remaining two pullback paths. Injectivity of transposition proves the equation.
No exchange is cancelled, and invertibility of either exchange is not required. -/
theorem compactSupportProperFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z' Z S' S : Scheme.{u}} {h : Z' ⟶ Z} {p' : Z' ⟶ S'}
    {p : Z ⟶ S} {a : S' ⟶ S} [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact p'] [QuasiSeparated p'] (sq : IsPullback p' h a p)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus A p).app K) ≫
      (mateEquiv
        (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p)
        (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p')
        ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso
            (upperStarCompIso (ModuleCat.{u + 1} A) sq.w) ≪≫
          Functor.mapDerivedCategoryPlusCompIso _ _).hom).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj K) ≫
      (lowerStar (ModuleCat.{u + 1} A) p').rightDerivedFunctorPlus.map
        ((fixedComparisonPullbackPlus A h).inv.app K) =
    (fixedComparisonPullbackPlus A a).inv.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) S').mapDerivedCategoryPlus.map
        ((Etale.baseChange (ModuleCat.{u + 1} A) sq.flip.toCommSq).app K) ≫
      (fixedComparisonDirectImageMatePlus A p').app
        ((Etale.upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus.obj K) := by
  have hh := cube
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p')
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p')
    (fixedComparisonPullbackPlus A p) (fixedComparisonPullbackPlus A p')
    (fixedComparisonPullbackPlus A a) (fixedComparisonPullbackPlus A h)
    (Etale.pullbackSquareComparison (ModuleCat.{u + 1} A) sq.flip.toCommSq).hom
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (upperStarCompIso (ModuleCat.{u + 1} A) sq.w) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _).hom
    (fixedComparisonDirectImageMatePlus A p) (fixedComparisonDirectImageMatePlus A p')
    (fixedComparisonDirectImageMatePlus_counit A p)
    (fixedComparisonDirectImageMatePlus_counit A p')
    (plus_square A sq) K
  rw [etale_mate_eq] at hh
  exact hh

end AlgebraicGeometry.ProEtale
