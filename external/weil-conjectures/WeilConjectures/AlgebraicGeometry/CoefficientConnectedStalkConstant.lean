/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.AlgebraicGeometry.CoefficientEtaleDerivedStalk
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.CoefficientConnectedLocalStalkModels
import WeilConjectures.AlgebraicGeometry.CoefficientEtaleStalkFlat
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.AlgebraicGeometry.CoefficientWeaklyContractibleLocalIso
import all WeilConjectures.AlgebraicGeometry.EtaleSectionGermIso
import all WeilConjectures.AlgebraicGeometry.LisseCoefficientConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.Topology.Connected.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # A single lisse complex on a connected component

Source: Stacks Project, Tags 09BI, 09C6 and 090K.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v w
open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.Scheme

/-- Exact constant realization followed by actual slice restriction for any coefficient
ring. Source: Stacks Tag 093J.
(auxiliary; not a blueprint node). -/
def coefficientSliceConstant (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    (U : coefficientProEtaleSiteModel.{u, v} X) :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
  commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
    max v (u + 1), max v (u + 1) + 1}
    (coefficientProEtaleModelTopology.{u, v} X) B ⋙
      adicResidueRestriction
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) U

private instance coefficientModuleLocallyBijective
    {C : Type*} [Category C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] :
    J.WEqualsLocallyBijective (ModuleCat.{w} B) := by
  have : ∀ V : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (equivSmallModel.{w} C).inverse.op)
        (ModuleCat.{w} B) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := ModuleCat.{w} B)

private theorem coefficient_lisse_stalk_finite
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : ConstantCompletion.Mod
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hF : SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B F) :
    Module.Finite B ((coefficientEtaleModuleStalk X B x).obj F) := by
  classical
  let e : X.Etale ≌ smallModelComparisonEtaleSite.{u, v} X := AsSmall.equiv
  let J := smallModelComparisonEtaleTopology.{u, v} X
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite J X.smallEtaleTopology := by
    change (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      (AsSmall.down.inducedTopology X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  let G := (e.sheafCongr X.smallEtaleTopology J (ModuleCat.{max v (u + 1)} B)).inverse
  let H := (coefficientModelFixedScalars J B).obj F
  have hl := fixed_lisse J B F hF
  let T := Scheme.Etale.mk (𝟙 X)
  obtain ⟨S, hS, hm⟩ := hl (e.functor.obj T)
  have hS' : S.functorPullback e.functor ∈ X.smallEtaleTopology T :=
    e.functor.cover_lift X.smallEtaleTopology J hS
  let t : (pointSmallEtale x).fiber.obj T := Over.homMk x (by simp [T])
  obtain ⟨V, f, hf, y, hy⟩ := (pointSmallEtale x).jointly_surjective _ hS' t
  obtain ⟨M, hM, ⟨em⟩⟩ := hm (e.functor.obj V) (e.functor.map f) hf
  let ei := Over.postEquiv (X := V) e
  have : ei.functor.IsCocontinuous (X.smallEtaleTopology.over V)
      (J.over (e.functor.obj V)) := by
    change (Over.post (X := V) e.functor).IsCocontinuous _ _
    infer_instance
  have : ei.inverse.IsCocontinuous (J.over (e.functor.obj V))
      (X.smallEtaleTopology.over V) := by
    change (Over.post (X := e.functor.obj V) e.inverse ⋙
      Over.map (e.unitIso.inv.app V)).IsCocontinuous _ _
    have : (Over.map (e.unitIso.inv.app V)).IsCocontinuous
        (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj V)))
        (X.smallEtaleTopology.over V) := by
      constructor
      intro A R hR
      change Sieve.overEquiv A (R.functorPullback _) ∈ X.smallEtaleTopology A.left
      rw [Sieve.overEquiv_functorPullback_map]
      exact hR
    exact isCocontinuous_comp _ _ (J.over (e.functor.obj V))
      (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj V)))
  have : ei.inverse.IsDenseSubsite (J.over (e.functor.obj V))
      (X.smallEtaleTopology.over V) := ei.isDenseSubsite_inverse_of_isCocontinuous _ _
  have : HasWeakSheafify (X.smallEtaleTopology.over V)
      (ModuleCat.{max v (u + 1)} B) :=
    -- The tip instances `Etale.locallySmall`/`Etale.essentiallySmall` (fixed universe `u + 1`)
    -- get stuck on `max v (u + 1)`; give the size instances explicitly.
    have : Small.{max v (u + 1)} (Over V) := small_max.{max v (u + 1), u + 1} _
    have : LocallySmall.{max v (u + 1)} (Over V) := locallySmall_max.{max v (u + 1), u, u + 1}
    have : EssentiallySmall.{max v (u + 1)} (Over V) := essentiallySmall_of_small_of_locallySmall _
    sfbSheafTensor_hasWeakSheafify (X.smallEtaleTopology.over V)
  let Gi : Sheaf (J.over (e.functor.obj V)) (ModuleCat.{max v (u + 1)} B) ⥤
      Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{max v (u + 1)} B) :=
    ei.functor.sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} B)
    (X.smallEtaleTopology.over V) (J.over (e.functor.obj V))
  let c : (Functor.whiskeringLeft _ _ (ModuleCat.{max v (u + 1)} B)).obj ei.functor.op ⋙
      presheafToSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max v (u + 1)} B) ≅
      presheafToSheaf (J.over (e.functor.obj V)) (ModuleCat.{max v (u + 1)} B) ⋙ Gi :=
    ei.functor.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{max v (u + 1)} B) (X.smallEtaleTopology.over V)
    (J.over (e.functor.obj V))
  let em' : (G.obj H).over V ≅
      (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max v (u + 1)} B)).obj M :=
    Gi.mapIso em ≪≫ (c.app ((Functor.const _).obj M)).symm
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{max v (u + 1)} B)) :=
    preservesFilteredColimitsOfSize_shrink.{u, max v (u + 1), u, max v (u + 1)} _
  let es : ((pointSmallEtale x).sheafFiber
      (A := ModuleCat.{max v (u + 1)} B)).obj (G.obj H) ≅ M :=
    (GrothendieckTopology.Point.restrictionStalkIso (pointSmallEtale x) y (G.obj H)).symm ≪≫
    ((pointSmallEtale x).over y).sheafFiber.mapIso em' ≪≫
    ((pointSmallEtale x).over y).sheafFiberConstantSheafIso M
  let := hM
  exact Module.Finite.equiv es.toLinearEquiv.symm

private theorem exactFunctor_perfect_of_flat_model
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (B : Type w) [CommRing B] [IsNoetherianRing B]
    (F : C ⥤ ModuleCat.{w} B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (P : CochainComplex C ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (eP : DerivedCategory.Q.obj P ≅ K)
    (hflat : ∀ q, Module.Flat B (F.obj (P.X q)))
    (hfinite : ∀ q, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} B) q).obj
        (F.mapDerivedCategory.obj K))) :
    DerivedCategory.IsPerfect (F.mapDerivedCategory.obj K) := by
  let P' := (F.mapHomologicalComplex (.up ℤ)).obj P
  let e : F.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P' :=
    (F.mapDerivedCategory.mapIso eP).symm ≪≫ F.mapDerivedCategoryFactors.app P
  exact DerivedCategory.isPerfect_of_flat_of_finite_homology P' a b hflat e hfinite

private theorem coefficient_lisse_derived_stalk_finite
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B] [IsNoetherianRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B
      ((coefficientModelCohomology _ q).obj K))
    (q : ℤ) :
    Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{max v (u + 1)} B) q).obj
      ((coefficientEtaleDerivedStalk X B x).obj K)) := by
  let R := ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let F := coefficientEtaleModuleStalk X B x
  let e : F.obj ((coefficientModelCohomology R q).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v (u + 1)} B) q).obj
        ((coefficientEtaleDerivedStalk X B x).obj K) :=
    (F.mapDerivedCategoryHomologyFunctorIso q).app K
  exact (Module.Finite.equiv_iff e.toLinearEquiv).mp
    (coefficient_lisse_stalk_finite X B x
      ((coefficientModelCohomology R q).obj K) (hlisse q))

private theorem coefficient_stalk_perfect
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B] [IsNoetherianRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B
      ((coefficientModelCohomology _ q).obj K))
    (a b : ℤ)
    (hTor : HasCoefficientModelTorAmplitude
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) K a b) :
    DerivedCategory.IsPerfect ((coefficientEtaleDerivedStalk X B x).obj K) := by
  let R := ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let F := coefficientEtaleModuleStalk X B x
  obtain ⟨P, hPge, hPle, hPflat, ⟨eP⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R K a b hTor.1).mp hTor
  let := hPge
  let := hPle
  exact exactFunctor_perfect_of_flat_model B F K P a b eP
    (fun q ↦ coefficientEtaleModuleStalk_flat X B x (P.X q) (hPflat q))
    (coefficient_lisse_derived_stalk_finite X B x K hlisse)

/-- A bounded lisse finite-type etale complex of finite Tor amplitude has a perfect
geometric stalk. On an affine weakly contractible object mapping into the connected
component of that point, its comparison pullback is the constant realization of
that specified stalk. This assertion concerns one complex over one ring.
Source: Stacks Project, Etale Cohomology, Tag 09BI; Pro-etale Cohomology, Tag 09C6,
first paragraph; Sites, Tag 090K.
(auxiliary; not a blueprint node).

Proof: the component of z is open in the locally Noetherian scheme. Restrict the
complex to this nonempty connected open. Constant-scalar restriction and the AsSmall
site equivalence identify the input with a bounded etale complex with finite locally
constant cohomology; they preserve tensor, cohomology and the Tor interval. The
connected perfect-constancy argument applies: bounded locally constant finite
cohomology gives local bounded finite-module complex models. Exact stalks identify
the models on intersecting images. Those images are open, and connectedness gives
one isomorphism class, represented by the stalk at the algebraic closure of the
residue field of z. Finite constant charts give finite stalk cohomology. The coefficient
Tor-amplitude criterion supplies a bounded flat representative of K. Taking the exact
stalk termwise preserves both its bounds and flatness. A bounded flat complex with
finite cohomology over a Noetherian ring is perfect. Pull the etale constant-model
cover to the given pro-etale object. Weak contractibility splits its covering
surjection; after a disjoint clopen refinement the constant models glue, and pulling
along the section gives constancy on the object. Weakly etale localization identifies
its small pro-etale site with the actual slice. Transport back through the exact
fixed-scalar and AsSmall equivalences; their constant comparisons give exactly the
functors in the conclusion. The image hypothesis provides the factorization through
the component open. An empty test object is harmless, since its slice sheaf category
is trivial. No tower, complete coefficient ring, or compatible markings are used. -/
theorem coefficient_connected_stalk_constant
    (X : Scheme.{u}) [IsNoetherian X]
    (B : Type (max v (u + 1))) [CommRing B] [IsNoetherianRing B]
    (z : X) (U : coefficientProEtaleSiteModel.{u, v} X)
    (hU : IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
      U).left)
    (hweak : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (himage : Set.range
      (((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj U).hom.base) ⊆
        connectedComponent z)
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((coefficientModelCohomology _ q).obj K))
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B
      ((coefficientModelCohomology _ q).obj K))
    (a b : ℤ)
    (hTor : HasCoefficientModelTorAmplitude
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) K a b) :
    DerivedCategory.IsPerfect
      ((coefficientEtaleDerivedStalk X B (X.algClosurePoint z)).obj K) ∧
    Nonempty
      ((coefficientSliceConstant X B U).obj
          ((coefficientEtaleDerivedStalk X B (X.algClosurePoint z)).obj K) ≅
        (adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) U).obj
            ((adicFinitePullback.{u, v} X B).obj K)) := by
  constructor
  · exact coefficient_stalk_perfect X B (X.algClosurePoint z) K hlisse a b hTor
  · dsimp only [coefficientSliceConstant, Functor.comp_obj]
    let E := (coefficientEtaleDerivedStalk X B (X.algClosurePoint z)).obj K
    let := HasDerivedCategory.standard (ConstantCompletion.Mod
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
    exact coefficient_weaklyContractible_local_iso X B U hU hweak
      ((commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
        max v (u + 1), max v (u + 1) + 1}
        (coefficientProEtaleModelTopology.{u, v} X) B).obj E)
      ((adicFinitePullback.{u, v} X B).obj K)
      (coefficient_connected_local_stalk_models X B z U himage K hbounded hlisse)

end AlgebraicGeometry.Scheme
