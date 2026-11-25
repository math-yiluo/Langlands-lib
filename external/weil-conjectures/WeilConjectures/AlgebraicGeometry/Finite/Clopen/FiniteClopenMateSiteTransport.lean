/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenAlphaSiteTransport

/-!
# Finite clopen proper/open mates under site comparison

Source: Stacks Project, Tags 099R, 09AF, 0F7B and 0B65; the explicit transpose
calculation of the DAG node (blueprint: lem-cbc-finite-clopen-mate-site-transport).

The alphas are constructed on sheaves from open-unit base change and the clopen
projection, then localized. Their proper mates are defined independently on both sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

private theorem transport_mate
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
    {L : C ⥤ D} {R : D ⥤ C} {K : E ⥤ F} {S : F ⥤ E}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {K' : E' ⥤ F'} {S' : F' ⥤ E'}
    (a : L ⊣ R) (b : K ⊣ S) (a' : L' ⊣ R') (b' : K' ⊣ S')
    (AC : C ⥤ C') (AD : D ⥤ D') (AE : E ⥤ E') (AF : F ⥤ F')
    (al : L ⋙ AD ≅ AC ⋙ L') (ak : K ⋙ AF ≅ AE ⋙ K')
    (br : R ⋙ AC ⟶ AD ⋙ R') (bs : S ⋙ AE ⟶ AF ⋙ S')
    (og : G ⋙ AE ≅ AC ⋙ G') (oh : H ⋙ AF ≅ AD ⋙ H')
    (α : G ⋙ K ⟶ L ⋙ H) (α' : G' ⋙ K' ⟶ L' ⋙ H')
    (hr : ∀ X, al.hom.app (R.obj X) ≫ L'.map (br.app X) ≫
      a'.counit.app (AD.obj X) = AD.map (a.counit.app X))
    (hs : ∀ X, ak.hom.app (S.obj X) ≫ K'.map (bs.app X) ≫
      b'.counit.app (AF.obj X) = AF.map (b.counit.app X))
    (ha : ∀ X, AF.map (α.app X) ≫ oh.hom.app (L.obj X) ≫
      H'.map (al.hom.app X) = ak.hom.app (G.obj X) ≫
        K'.map (og.hom.app X) ≫ α'.app (AC.obj X)) (X : D) :
    og.hom.app (R.obj X) ≫ G'.map (br.app X) ≫
      (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α')).app (AD.obj X) =
    AE.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ α)).app X) ≫ bs.app (H.obj X) ≫
      S'.map (oh.hom.app X) := by
  apply (b'.homEquiv _ _).symm.injective
  change K'.map (_ ≫ _ ≫ _) ≫ b'.counit.app _ =
    K'.map (_ ≫ _ ≫ _) ≫ b'.counit.app _
  apply (cancel_epi (ak.hom.app (G.obj (R.obj X)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit]
  have hn := α'.naturality (br.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc (K'.map (G'.map (br.app X))), hn]
  simp only [Category.assoc]
  rw [← reassoc_of% (ha (R.obj X))]
  rw [← H'.map_comp, ← H'.map_comp, hr]
  have ho := oh.hom.naturality (a.counit.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at ho
  rw [← ho]
  have hc := b'.counit.naturality (oh.hom.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hc
  rw [hc]
  have hak := ak.hom.naturality
    ((mateEquiv a b (TwoSquare.mk _ _ _ _ α)).app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hak
  rw [← reassoc_of% hak]
  rw [reassoc_of% hs]
  rw [← AF.map_comp_assoc, ← AF.map_comp_assoc, mateEquiv_counit]
  rfl

namespace AlgebraicGeometry

namespace ProEtale

end ProEtale

namespace ProEtale

/-- Canonical site comparison carries the clopen alpha and its proper mate to the
corresponding pro-etale maps, with the finite etale and refinement normalizations.
Source: Stacks Tags 099R, 09AF, 0F7B and 0B65
(blueprint: lem-cbc-finite-clopen-mate-site-transport).

Proof plan (the seven steps of the node):
1. Properness makes p and r finite type and hence quasi-compact. Their closed
   diagonals are quasi-compact, giving quasi-separatedness. Exact k_! preserves
   cohomological lower bounds, so L and k_!L belong to the comparison domains.
   Apply the canonical direct-image mate theorem at (r,L) and (p,k_!L).
2. Compare the inverses of the two cartesian open comparisons under the open
   adjunction. Their transposes are the pulled-back open units followed by the
   cartesian pullback compositor. The canonical pullback and open comparisons
   respect these units and compositors; injectivity of transpose proves equality.
3. On the clopen image and its open complement, sheaf gluing characterizes the
   projection by (x,y) mapping to (x,0). Comparison respects both restrictions
   and extension by zero, hence this map, degreewise and after localization.
   No faithfulness of evaluation on the derived category is asserted.
4. Compose the beta equality, projector equality and canonical compositors to
   obtain the first displayed alpha equation. Etale clopen-mate normalization
   identifies the etale mate with the resolution-normalized finite interchange,
   including the identity-left/refinement case.
5. Transpose the left route of the mate equation under p's proper adjunction,
   precomposing with a_p. Naturality of alpha in b_r and the r-counit equation
   reduce it to o_k followed after A_W of J_k(epsilon_r) composed with alpha_e.
6. Transpose the right route with the same precomposition. Naturality of the
   pro-etale counit moves o_k outside. Naturality of a_p and its counit equation
   reduce to o_k after A_W of epsilon_p composed with G_p(gamma_e). The etale
   mate identity makes this the expression in step 5. Cancel a_p and transpose.
7. The open comparisons, b_r, b_p and normalized gamma_e are isomorphisms.
   Cancel their composites in the equation to deduce invertibility of the
   specified gamma_p at A_V L. All normalizations were fixed before mating.
These steps use the named canonical-mate, pullback and open-comparison dependencies,
etale/pro-etale extension-zero base change, separated-implies-quasi-separated,
and the finite proper/open coherence and clopen normalization nodes.
-/
theorem finiteClopenMateSiteTransport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    QuasiCompact p ∧ QuasiSeparated p ∧ QuasiCompact r ∧ QuasiSeparated r ∧
    (∀ (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategoryPlus.map
          ((Etale.ClopenMateNormalization.derivedAlphaPlus Λ k r p i h).app M) ≫
        (properOpenSiteExtensionIso Λ k).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus.obj M) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus Λ r).hom.app M) =
      (fixedComparisonPullbackPlus Λ p).hom.app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus.map
          ((properOpenSiteExtensionIso Λ i).hom.app M) ≫
        (cbcClopenAlphaPlus Λ k i r p h).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategoryPlus.obj M)) ∧
    (∀ (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h).app L =
        (Etale.ClopenMateNormalization.normalizedComparison Λ k r p i h).hom.app L ∧
      (properOpenSiteExtensionIso Λ i).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj L) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
          ((fixedComparisonDirectImageMatePlus Λ r).app L) ≫
        (cbcClopenMatePlus Λ k i r p h).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj L) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus.map
          ((Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h).app L) ≫
        (fixedComparisonDirectImageMatePlus Λ p).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso Λ k).hom.app L) ∧
      IsIso ((fixedComparisonDirectImageMatePlus Λ r).app L) ∧
      IsIso ((fixedComparisonDirectImageMatePlus Λ p).app
        ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L)) ∧
      IsIso ((Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h).app L) ∧
      IsIso ((cbcClopenMatePlus Λ k i r p h).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj L))) := by
  have hp : QuasiCompact p := inferInstance
  have hps : QuasiSeparated p := inferInstance
  have hr : QuasiCompact r := inferInstance
  have hrs : QuasiSeparated r := inferInstance
  have ha := finiteClopenAlphaSiteTransport Λ k i r p h
  refine ⟨hp, hps, hr, hrs, ha, ?_⟩
  intro L
  have hn := congr_app
    (Etale.ClopenMateNormalization.etaleClopenMateNormalization Λ k r p i h).2.1 L
  have := isIso_fixedComparisonDirectImageMatePlus Λ r
  have := isIso_fixedComparisonDirectImageMatePlus Λ p
  have hbr : IsIso ((fixedComparisonDirectImageMatePlus Λ r).app L) := by
    infer_instance
  have hbp : IsIso ((fixedComparisonDirectImageMatePlus Λ p).app
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L)) := by
    infer_instance
  have hge : IsIso ((Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h).app L) := by
    rw [hn]
    infer_instance
  have heq := transport_mate
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).derivedPlus
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).derivedPlus
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) p)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategoryPlus
    (fixedComparisonPullbackPlus Λ r) (fixedComparisonPullbackPlus Λ p)
    (fixedComparisonDirectImageMatePlus Λ r) (fixedComparisonDirectImageMatePlus Λ p)
    (properOpenSiteExtensionIso Λ i) (properOpenSiteExtensionIso Λ k)
    (Etale.ClopenMateNormalization.derivedAlphaPlus Λ k r p i h)
    (cbcClopenAlphaPlus Λ k i r p h)
    (fun K ↦ ?_) (fun K ↦ ?_) ha L
  · have heq' : (properOpenSiteExtensionIso Λ i).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj L) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
          ((fixedComparisonDirectImageMatePlus Λ r).app L) ≫
        (cbcClopenMatePlus Λ k i r p h).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj L) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus.map
          ((Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h).app L) ≫
        (fixedComparisonDirectImageMatePlus Λ p).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso Λ k).hom.app L) := by
      simpa only [Etale.ClopenMateNormalization.derivedMatePlus, cbcClopenMatePlus,
        Etale.rightDerivedLowerStarPlus] using heq
    clear heq
    have heq := heq'
    have hcomp : IsIso
        ((properOpenSiteExtensionIso Λ i).hom.app
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj L) ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
            ((fixedComparisonDirectImageMatePlus Λ r).app L) ≫
          (cbcClopenMatePlus Λ k i r p h).app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj L)) := by
      rw [heq]
      infer_instance
    have hgp : IsIso ((cbcClopenMatePlus Λ k i r p h).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj L)) :=
      (isIso_comp_left_iff
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
          ((fixedComparisonDirectImageMatePlus Λ r).app L)) _).mp
        ((isIso_comp_left_iff
          ((properOpenSiteExtensionIso Λ i).hom.app
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj L)) _).mp hcomp)
    exact ⟨hn, heq, hbr, hbp, hge, hgp⟩
  · simpa only [Etale.rightDerivedLowerStarPlus, Etale.derivedUpperStarLowerStarAdjunctionPlus,
      Adjunction.derivedAdjunctionPlus_eq_derivedPlus] using
      fixedComparisonDirectImageMatePlus_counit Λ r K
  · simpa only [Etale.rightDerivedLowerStarPlus, Etale.derivedUpperStarLowerStarAdjunctionPlus,
      Adjunction.derivedAdjunctionPlus_eq_derivedPlus] using
      fixedComparisonDirectImageMatePlus_counit Λ p K

end ProEtale

end AlgebraicGeometry
