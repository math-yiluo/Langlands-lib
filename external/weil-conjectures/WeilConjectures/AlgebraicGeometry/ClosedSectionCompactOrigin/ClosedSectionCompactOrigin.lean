/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ClosedSectionCompactOrigin.ClosedSectionCompactOriginData
import WeilConjectures.AlgebraicGeometry.ClosedSectionCompactOrigin.ClosedSectionSourceNormalization
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport

/-! # Identity-normalized compact origin of a closed-section map

Source: current blueprint, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 1, induced global morphism;
Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-pur-closed-section-compact-origin).

The source identifications are assembled from the published proper, composition and
identity comparisons. The given compactification is retained throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ProEtale
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorIso
  CategoryTheory.Functor.mapDerivedCategorySingleFunctor
  AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
  AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoOfIsProper

namespace AlgebraicGeometry.ClosedSectionCompactOrigin
variable (P : WeilConjectures.PurityFiniteSetting.{u})

local instance transportCoefficientFinite : Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm
attribute [local irreducible] WeilConjectures.PurityFiniteSetting.Coefficient
  WeilConjectures.PurityFiniteSetting.Ring

set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] constantComparison supportedComparison etaleClosedIso proClosedIso
  compactComparison compactSupportSiteComparison originCompositionAmbient originCompactSupportId
  towerCandidateComparison proSigma etaleSigma etaleTau proTau targetComparison
  originComposition

private lemma compact_comparison_naturality {X Y : Scheme.{u}} {v : X ⟶ Y}
    (c : Compactification v)
    {L M : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))} (t : L ⟶ M) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} P.Coefficient) c).map t)) ≫
        (compactComparison P c M).hom =
      (compactComparison P c L).hom ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).map
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              (DerivedCategory.Plus.ι.map t)) := by
  simpa only [compactExchangeTransportComparison, compactComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc] using
    (compactExchangeTransportComparison P.Coefficient c).hom.naturality t

/-- The identity-normalized source equation and transport of the given closed-section map.
Source: current blueprint, thm-pur-rank-one-thom.proof.md, Step 1; Stacks 0F7B, 0F7J
(blueprint: lem-pur-closed-section-compact-origin).

Proof, following the node's ten steps:
1. Exact etale extension by zero preserves a lower cohomological bound. Resolve its
bounded-below output by bounded-below injectives (lem-weil-pbc-module-sheaves-enough-injectives,
lem-weil-pbc-dplus-injective-representative). They are K-injective, and total derived proper
image is their termwise image, still bounded below (lem-weil-pbc-kinjective-total-derived).
2. The section is proper. Finite type over the field makes B, X and the compactification
ambient Noetherian. Etale closed image is exact; pro-etale closed image is exact for a
quasi-compact open complement. The identity-open comparison removes identity extension,
and exact-derived single-complex comparison gives the displayed closed identifications.
3. The identity-open site comparison identifies beta_s with the named direct-image counit
mate. Supported-constant normalization identifies epsilon_s with that mate followed by
s_* of chi, by its constant-restriction characterization; the identity-open comparison is
identity after removing identity extension.
4. Compose the inverse closed identification, the published compact-support compositor,
the section equality and the canonical identity comparison. These are etaleSigma and
proSigma, including the canonical comparisons from the specified compactification c.
5. Write c=(j,r) and t=sj. The proper-to-separated-target triangle makes t proper because
rt=id. The square (id,s,t,j) is Cartesian: t factors through the open j. This supplies a
compatible tower for exactly c, with identity inner and composite opens.
6. The unbounded etale composition and pro-etale tower-normalization statements identify
both compositors with Sigma = v D_(r,t) P_r(Gamma), where Gamma is the open adjunct of
inverse open-restriction exchange. Remove the inner identity extensions. Naturality at
chi extends the pro-etale formula from C_B A_B^e to A_B^p.
7. Apply the site clause of lem-sp-proper-open-coefficient-mate to this square: since the
top open is identity, b_t C(Gamma_e) = Gamma_p J_j(b_s) e_j. The specified inverse compact
comparison is beta_N = P_r(e_j) b_r on the same compactification.
8. Expand Sigma_p F^p(b_s) beta. The preceding square and naturality of b_r replace its
middle factors by P_r(b_t) b_r C(Gamma_e). Composite compatibility of the named mate then
gives b_(rt) C(D_(r,t) Gamma_e). Identity compatibility removes b_id; naturality at chi
and epsilon_s = P_s(chi) b_s give exactly the first displayed equation below.
9. Naturality of beta at the actual ce, followed by F^p(theta) and the assumed class-map
square, gives psi C(F^e ce) = F^p(cp) F^p(epsilon_s) beta_source. Psi is an isomorphism
because theta and beta are isomorphisms (proposition-comparison-immersions--4).
10. Precompose with C(sigma_e inverse) and use step 8 to cancel the two sigma factors.
The result is psi C(tau_e) = tau_p chi. The degree-zero source and bounded-below target,
with sourceWitness and targetWitness, retain the actual antecedent and map tau_e.
No cancellation or invertibility assumption is applied to ce, cp or either tau. -/
theorem closed_section_compact_origin {B X : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] (hs : s ≫ f = 𝟙 B) :
    (compactComparison P c (etaleSource P s)).hom ≫
        (ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).map (supportedComparison P s).hom ≫
        (proSigma P f c s hs).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (etaleSigma P f c s hs).hom) ≫
        (constantComparison P B).hom ∧
    ∀ (M : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (theta : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        X).mapDerivedCategory.obj M.obj ≅ K.obj)
      (ce : etaleSource P s ⟶ M) (cp : (proSource P s).obj ⟶ K.obj),
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map ce) ≫ theta.hom =
        (supportedComparison P s).hom ≫ cp →
      DerivedCategory.TStructure.t.plus
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).obj M.obj) ∧
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (etaleTau P f c s hs ce)) ≫
          (targetComparison P c M K theta).hom =
        (constantComparison P B).hom ≫ proTau P f c s hs cp := by
  let CB := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let CX := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let Fe := Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} P.Coefficient) c
  let Fp := ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) c
  have hsource := closedSectionSourceNormalization P b f c s hs
  refine ⟨hsource, ?_⟩
  intro M K theta ce cp hclass
  constructor
  · exact DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} P.Coefficient) c).app M)
      (Fe.obj M).property
  · have hn :
        CB.map (DerivedCategory.Plus.ι.map (Fe.map ce)) ≫
            (compactComparison P c M).hom =
          (compactComparison P c (etaleSource P s)).hom ≫
            Fp.map (CX.map (DerivedCategory.Plus.ι.map ce)) := by
      exact compact_comparison_naturality P c ce
    have hc :
        CB.map (DerivedCategory.Plus.ι.map (Fe.map ce)) ≫
            (targetComparison P c M K theta).hom =
          (compactComparison P c (etaleSource P s)).hom ≫
            Fp.map (supportedComparison P s).hom ≫ Fp.map cp := by
      simp only [targetComparison, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, hn, Category.assoc, ← Fp.map_comp, hclass,
        Fp.map_comp]
    have hi :
        CB.map (DerivedCategory.Plus.ι.map (etaleSigma P f c s hs).inv) ≫
            (compactComparison P c (etaleSource P s)).hom ≫
            Fp.map (supportedComparison P s).hom =
          (constantComparison P B).hom ≫ (proSigma P f c s hs).inv := by
      apply (cancel_mono (proSigma P f c s hs).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hsource, ← CB.map_comp_assoc, ← DerivedCategory.Plus.ι.map_comp,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id, CB.map_id, Category.id_comp]
    simp only [etaleTau, proTau]
    rw [Functor.map_comp, CB.map_comp, Category.assoc, hc]
    simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ Fp.map cp) hi

end AlgebraicGeometry.ClosedSectionCompactOrigin
