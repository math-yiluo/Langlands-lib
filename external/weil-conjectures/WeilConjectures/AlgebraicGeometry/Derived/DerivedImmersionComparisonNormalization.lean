/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison

/-!
# Restriction normalization of derived immersion comparisons

Source: blueprint main-20261015, proof of `proposition-six-operations-dctf--15`,
second paragraph; Stacks Tags 09AF, 09BM, 09AA, 015F and 0FND
(blueprint: lem-sf-derived-immersion-comparison-normalization).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v h w u

open CategoryTheory Limits

namespace CategoryTheory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open SheafOfModules.OpenTensorNormalization in
private theorem exact_hom_fac
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    (exactDerivedAdjunction a).homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  have hu : (exactDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [exactDerivedAdjunction, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

namespace Functor

private theorem exactSquare_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hc := mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact hc.symm
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]

end Functor

open SheafOfModules.OpenTensorNormalization in
private theorem exact_mate
    {A B C D : Type v} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (d : R₁ ⋙ G ≅ H ⋙ R₂) (b : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hb : ∀ P, a₂.unit.app (G.obj P) ≫ R₂.map (b.hom.app P) =
      G.map (a₁.unit.app P) ≫ d.hom.app (L₁.obj P)) :
    ((mateEquiv (exactDerivedAdjunction a₁) (exactDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)) =
        (Functor.mapDerivedCategorySquareIso b).hom := by
  have hι (K : CochainComplex A ℤ) :
      (a₂.mapHomologicalComplex (.up ℤ)).homEquiv
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((H.mapHomologicalComplex (.up ℤ)).obj ((L₁.mapHomologicalComplex (.up ℤ)).obj K))
          ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app K) =
        (G.mapHomologicalComplex (.up ℤ)).map
            ((a₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
            ((L₁.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hb (K.X n)
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (H.mapDerivedCategory.map (L₁.mapDerivedCategoryFactors.hom.app K) ≫
    H.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have hc := derivedMate_comparison
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ))
    (exactDerivedAdjunction a₁) (exactDerivedAdjunction a₂)
    L₁.mapDerivedCategoryFactors.hom L₂.mapDerivedCategoryFactors.hom
    R₁.mapDerivedCategoryFactors R₂.mapDerivedCategoryFactors
    G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors
    (exact_hom_fac a₁) (exact_hom_fac a₂)
    (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex d.hom (.up ℤ)))
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)
    (Functor.exactSquare_fac d) (NatTrans.mapHomologicalComplex b.hom (.up ℤ)) hι K
  exact hc.trans (Functor.exactSquare_fac b K).symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Open etale restriction is also a left adjoint, hence preserves colimits.
Source: Stacks Tag 03DI; the existing restriction/direct-image adjunction
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
instance derivedImmersionEtaleRestriction_isLeftAdjoint (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).IsLeftAdjoint :=
  (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint

/-- Open pro-etale restriction is also a left adjoint, hence preserves colimits.
Source: Stacks Tag 09AE; the existing restriction/direct-image adjunction
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
instance derivedImmersionProEtaleRestriction_isLeftAdjoint (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).IsLeftAdjoint :=
  (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint

/-- Termwise canonical pullback comparison in open-restriction form, using the exact
composition identifications. Source: Stacks Tags 09AF and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionOpenPullbackComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openComparisonRestrictionIso A j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Termwise descent of the specified canonical open extension comparison.
Source: Stacks Tags 09AF and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionOpenExtensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Etale closed direct image is exact; left exactness is already supplied by its
right-adjoint structure. Source: Stacks Tags 04CA and 08M3
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: identify the etale topos of the closed subscheme with the closed complement
topos. Its direct image on modules is exact and fully faithful, with invertible
restriction counit, as in lem-trf-oriented-closed-base-localization. -/
@[instance] theorem derivedImmersionClosedEtale_exact (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) h) := by
  infer_instance

/-- Pro-etale closed direct image is exact over a Noetherian target; its left
exactness is the right-adjoint structure. Source: Stacks Tag 09BM
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: the complement open immersion is quasi-compact: every open in a Noetherian
scheme is quasi-compact. Apply proposition-extension-zero-restriction-closed-subscheme--4 to this
complement. No constructibility hypothesis is used. -/
@[instance] theorem derivedImmersionClosedProEtale_exact (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) h) := by
  let V : X.Opens :=
    ⟨(Set.range h.base)ᶜ, h.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : IsCompl (Set.range h.base) (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  exact preservesFiniteColimits_lowerStar_of_isCompl (R := A) h V.ι hV

/-- The ordinary closed comparison is the specified counit transpose, not an
independently chosen isomorphism. Source: Stacks Tag 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: the direct-image comparison is the double mate of the sectionwise comparison
of direct images. The iterated-mate identity identifies it with the mate of the
canonical pullback comparison. Applying the inverse-transpose counit formula gives
exactly the asserted component formula. -/
theorem derivedImmersionClosed_sheaf_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)).app F =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _)
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) h).hom.app
            ((Etale.lowerStar (ModuleCat.{u + 1} A) h).obj F) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Z).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).counit.app F)) := by
  let ad := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
  let e := ad.homEquiv
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) h).obj F))
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)
  change _ = e _
  apply e.symm.injective
  rw [Equiv.symm_apply_apply]
  change (upperStar (ModuleCat.{u + 1} A) h).map
      ((lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)).app F) ≫
      ad.counit.app _ = _
  have hm := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)) F
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z)
    (lowerStarCompComparisonLowerStarIso h (ModuleCat.{u + 1} A)).inv
  unfold lowerStarComparisonUpperStarBaseChange at hm
  rw [hi] at hm
  exact hm

end AlgebraicGeometry.ProEtale
