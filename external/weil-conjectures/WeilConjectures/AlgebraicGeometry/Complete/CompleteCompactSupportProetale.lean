/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGammaIsIso
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeCoherence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.Compactification.Cofiltered
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryOpenExchangeIdentity
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection

import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Clopen.ClopenScalarRestrictionReverseAdjunction
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenFiniteEtaleOrigins
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates

/-!
# Complete pro-etale compact-support base change

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
node proposition-composition-base-change-rf-shriek--4 (blueprint:
proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
section RefinementGamma

-- Keep the module-category instances of the proper/open comparisons, so that the
-- components below are syntactically those of `cbcProperOpenGamma`.
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived flatConstantModulesAbelian

/-- The proper/open gamma of a refinement, for the identity on the open part.
Source: blueprint proof step 8, C_u (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
@[irreducible]
def cbcRefinementGamma {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :=
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  cbcProperOpenGamma d c₁.i (𝟙 X) u.hom c₂.i (u.i_hom.trans (Category.id_comp _).symm)

/-- The refinement gamma preceded by the inverse proper identity comparison.
Source: blueprint proof step 8, C_u (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
@[irreducible]
def cbcRefinementGammaComp {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :=
  Functor.whiskerRight (d.pushId X).inv (cbcJ d c₂.i) ≫ cbcRefinementGamma d u

private theorem cbcIsIso_app_comp {C E : Type*} [Category C] [Category E] {F G H : C ⥤ E}
    (α : F ⟶ G) (β : G ⟶ H) (x : C) (hα : IsIso (α.app x)) (hβ : IsIso (β.app x)) :
    IsIso ((α ≫ β).app x) := by
  rw [NatTrans.comp_app]
  exact IsIso.comp_isIso' hα hβ

private theorem cbcIsIso_whiskerRight_app {C D E : Type*} [Category C] [Category D]
    [Category E] {F G : C ⥤ D} (α : F ⟶ G) (P : D ⥤ E) (x : C) (hα : IsIso (α.app x)) :
    IsIso ((Functor.whiskerRight α P).app x) := by
  rw [Functor.whiskerRight_app]
  exact Functor.map_isIso P _

private theorem cbcIsIso_app_of_isIso {C E : Type*} [Category C] [Category E] {F G : C ⥤ E}
    (α : F ⟶ G) [IsIso α] (x : C) : IsIso (α.app x) := inferInstance

/-- Precomposing the refinement gamma with the proper identity comparison keeps it invertible.
Source: blueprint proof step 8, C_u (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcRefinementGammaComp_app_isIso {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X)
    (h : IsIso ((cbcRefinementGamma d u).app K)) :
    IsIso ((cbcRefinementGammaComp d u).app K) := by
  unfold cbcRefinementGammaComp
  exact cbcIsIso_app_comp _ _ _ (cbcIsIso_app_of_isIso _ _) h

end RefinementGamma



section

attribute [local irreducible] cbcDerivedOpenShriek cbcProperOpenGamma
  AdicCoefficientDatum.pushComp AdicCoefficientDatum.pushId HasDerivedCategory.standard

/-- The canonical proper/open refinement comparison as a natural transformation.
Its components are the proper pushforward of gamma, preceded by the inverse proper
identity comparison and followed by the proper composition comparison. Explicit
unitors and associators have identity components, so this construction gives the
same component formula as the canonical refinement map.
Source: blueprint proof step 8, C_u; Stacks 0F7B and 0F7C
(blueprint: def-cbc-completed-refinement-transformation). -/
@[irreducible]
def cbcRefinementTransformation
    {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    cbcSupport d c₂ ⟶ cbcSupport d c₁ :=
  Functor.whiskerRight (Functor.leftUnitor (cbcJ d c₂.i)).inv (d.push c₂.g) ≫
    Functor.whiskerRight (cbcRefinementGammaComp d u) (d.push c₂.g) ≫
    (Functor.associator (cbcJ d c₁.i) (d.push u.hom) (d.push c₂.g)).hom ≫
    Functor.whiskerLeft (cbcJ d c₁.i) (d.pushComp u.hom c₂.g).hom ≫
    Functor.whiskerLeft (cbcJ d c₁.i)
      (eqToIso (congrArg (fun f ↦ d.push f) u.hom_g)).hom

end

/-- The canonical refinement map, directed from the coarser to the finer compactification.
It is proper pushforward of gamma, with the proper identity and composition comparisons.
Source: blueprint proof step 8, C_u (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
def cbcRefinementMap {X Y : Scheme.{t}} {f : X ⟶ Y} [qf : QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X) :
    (cbcSupport d c₂).obj K ⟶ (cbcSupport d c₁).obj K :=
  (cbcRefinementTransformation d u).app K

/-- The refinement map is invertible as soon as its proper/open gamma component is.
The remaining factors are proper pushforward and the identity and composition comparisons.
Source: blueprint proof step 8, C_u (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcRefinementMap_isIso_of_gamma {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X)
    (h : IsIso ((cbcRefinementGamma d u).app K)) :
    IsIso (cbcRefinementMap d u K) := by
  unfold cbcRefinementMap cbcRefinementTransformation
  exact cbcIsIso_app_comp _ _ _ (cbcIsIso_app_of_isIso _ _) (cbcIsIso_app_comp _ _ _
    (cbcIsIso_whiskerRight_app _ _ _ (cbcRefinementGammaComp_app_isIso d u K h))
    (cbcIsIso_app_of_isIso _ _))

/-- The compatible-tower compact-support composition map. Its middle factor is the
specified proper/open gamma, so this is not an arbitrary isomorphism of the endpoints.
Source: blueprint proof step 8, D_j (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
def cbcCompositionMap {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [qh : QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h) (chf : Compactification (f ≫ h))
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    [IsOpenImmersion b] [QuasiCompact b] [IsProper p]
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g) (K : d.derived X) :
    (cbcSupport d ch).obj ((cbcSupport d cf).obj K) ⟶ (cbcSupport d chf).obj K :=
  letI : QuasiCompact ch.i := ch.quasiCompact_openImmersion inferInstance
  (d.push ch.g).map ((cbcProperOpenGamma d b cf.g p ch.i hp).app
      ((cbcJ d cf.i).obj K)) ≫
    (d.pushComp p ch.g).hom.app ((cbcJ d b).obj ((cbcJ d cf.i).obj K)) ≫
    (d.push (p ≫ ch.g)).map
      ((cbcJComp d cf.i b).hom.app K ≫ (cbcJCongr d hb).hom.app K) ≫
    (eqToIso (congrArg (fun f ↦ d.push f) hq)).hom.app ((cbcJ d chf.i).obj K)

/-- Composition for a supplied Cartesian compatible tower. The open immersion and
quasi-compactness of b are derived from that square and the outer compactification.
Source: blueprint proof step 8, compatible towers (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
def cbcTowerCompositionMap {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [qh : QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h) (chf : Compactification (f ≫ h))
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z) [IsProper p]
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g) (sq : IsPullback b cf.g p ch.i) (K : d.derived X) :
    (cbcSupport d ch).obj ((cbcSupport d cf).obj K) ⟶ (cbcSupport d chf).obj K :=
  letI : IsOpenImmersion b := MorphismProperty.of_isPullback sq.flip ch.isOpenImmersion
  letI : QuasiCompact b := MorphismProperty.of_isPullback sq.flip
    (ch.quasiCompact_openImmersion qh)
  cbcCompositionMap d cf ch chf b p hb hp hq K

private theorem cbcTowerComplete_of_property (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : cbcCompleteProperty d T r a ha K) :
    d.TowerComplete T K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)) at hK
  change IsIso (d.completionUnit T K)
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  rw [← hc]
  infer_instance

private theorem cbcCompletedExchange_naturality
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {K H : d.derived X} (k : K ⟶ H) :
    (d.completedPull g).map ((d.push f).map k) ≫ d.completedExchange sq H =
      d.completedExchange sq K ≫ (d.push f').map ((d.completedPull g').map k) := by
  let π : d.push f ⋙ completedReductionTower Y d ≅
      completedReductionTower X d ⋙ d.towerPush f :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection f K))
      (fun {K H} k ↦ (d.towerProjection_properties f K).2.1 H k)
  let e : d.push f ⋙ d.completedPull g ⟶ d.completedPull g' ⋙ d.push f' :=
    Functor.whiskerRight (Functor.whiskerRight π.hom (d.towerPull g))
      (completedRlim Y' (d.completedRing Y')) ≫
        Functor.whiskerRight (exchangeStrictNatTrans d sq)
          (completedRlim Y' (d.completedRing Y')) ≫
        Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
          (d.directImageRlimIso f').inv
  exact e.naturality k

/-- Every normalized proper/open refinement map is invertible on the stated inputs.
No Cartesian hypothesis is imposed on the refinement square.
Source: blueprint statement and proof step 8; Stacks 0F7B, 09C9
(blueprint: proposition-composition-base-change-rf-shriek--4).
Proof: pass to the strict quotient tower after constant-coefficient restriction. The
section and unit normalizations identify gamma with the strict proper/open gamma.
Finite evaluation is the normalized finite-coefficient proper/open map on the retained
bounded-below origins, hence invertible by finite compact-support base change. The
cone is acyclic levelwise, so gamma is invertible as an actual derived strict-tower
map. Apply Rlim and the specified open/limit and proper composition comparisons. -/
theorem cbcRefinementMap_isIso
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (cbcRefinementMap d u K.obj) := by
  apply cbcRefinementMap_isIso_of_gamma
  unfold cbcRefinementGamma
  exact @cbcProperOpenGamma_app_isIso _ _ d _ _ _ _ _ _ _ _ _ _ ?_ ?_ _ _ _ r a ha K _origins

/-- The canonical compactification comparison through any supplied common refinement.
Its factors are the specified proper/open refinement maps, not chosen endpoint isos.
Source: blueprint proof step 8, I_12 (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
def cbcCompactificationComparison
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₀ c₁ c₂ : Compactification f} (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (cbcSupport d c₁).obj K.obj ≅ (cbcSupport d c₂).obj K.obj :=
  @asIso _ _ _ _ (cbcRefinementMap d u₁ K.obj)
      (cbcRefinementMap_isIso d u₁ r a ha K origins) ≪≫
    (@asIso _ _ _ _ (cbcRefinementMap d u₂ K.obj)
      (cbcRefinementMap_isIso d u₂ r a ha K origins)).symm

section

attribute [local irreducible] cbcDerivedOpenShriek cbcProperOpenGamma
  cbcDerivedOpenAdjunction
  AdicCoefficientDatum.pullComp AdicCoefficientDatum.pullId
  AdicCoefficientDatum.pushComp AdicCoefficientDatum.pushId HasDerivedCategory.standard

-- The concrete derived categories make the kernel check of the iso composites expensive.
end

end AlgebraicGeometry.Scheme
