/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

import WeilConjectures.CategoryTheory.ModuleObjects.ResidueOrdinary.IntegralResidueOrdinaryMonoidal
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula

/-! # Pro-etale locality and pullback of dualizable condensed complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
pullback paragraph before (3.1), Definition 3.3 and Lemma 4.5
(blueprint: lem-zl-condensed-lisse-proetale-locality).

The ordinary unbounded derived categories and their ordinary derived tensor are the
published internal-module constructions. Lisse means `Nonempty (HasRightDual K)`;
`HasRightDual` includes an exact evaluation/coevaluation pairing with both triangle identities.
No quasi-compactness or condition on irreducible components is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Register the existing Koszul braiding of the ordinary derived tensor on internal modules.
This is the generic published construction specialized to the coefficient module category;
it selects no arbitrary braiding or new tensor structure.
Source: HRS Section 3, ordinary symmetric derived tensor
(blueprint: lem-zl-condensed-lisse-proetale-locality). -/
noncomputable instance condensedDerivedBraiding
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :=
  DerivedCategory.braidedCategory' _

/-- Inverse image along any scheme morphism, using the canonical coefficient identification,
is exact and strong symmetric monoidal. Between symmetric categories, `Functor.Braided`
is exactly strong symmetric monoidality, including invertible tensor and unit comparisons.
Source: HRS Section 3, paragraph before (3.1)
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG step 1): `condensedPullbackHom` is the component at Λ of the monoidal comparison
`upperStarFromPointComp`, hence a ring isomorphism. The published module inverse image
extends scalars along this exact map and is exact. Its termwise derived functor is
triangulated. Use the explicit balanced-tensor monoidal structure and braiding of
IntegralResidueOrdinaryMonoidal. InverseImageModuleFlat proves preservation of flat modules.
The generic left-derived monoidal construction then supplies a braided structure on LF.
Transport it along the canonical comparison LF ≅ D(F), using the induced monoidal
natural isomorphism to transport the braided axiom. -/
theorem condensed_derivedPullback_exact_symmetricMonoidal
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T X : Scheme.{u}} (f : T ⟶ X) :
    (CondensedRing.upperStar Λ.X f).mapDerivedCategory.IsTriangulated ∧
      Nonempty (CondensedRing.upperStar Λ.X f).mapDerivedCategory.Braided := by
  classical
  let F := CondensedRing.upperStar Λ.X f
  let := CondensedRing.residueOrdinaryUpperStarMonoidal Λ.X f
  have hflat : F.PreservesFlat := by
    have hf := inverseImageModule_preservesFlat f (condensedRingObj Λ.X X)
      (condensedRingObj Λ.X T) (asIso (condensedPullbackHom Λ.X f)).inv
    refine ⟨fun {M} hM ↦ ?_⟩
    exact ObjectProperty.flat.prop_of_iso
      ((Functor.isoWhiskerLeft
        ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f))).app M).symm
      (hf.flat_obj hM)
  let := hflat
  let b := F.leftDerivedFunctorBraided
    (CondensedRing.residueOrdinaryUpperStar_braiding Λ.X f)
  let := b
  let : F.leftDerivedFunctor.Monoidal := b.toMonoidal
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  let := Functor.Monoidal.transport e
  let : NatTrans.IsMonoidal e.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport e
  exact ⟨inferInstance, ⟨{
    braided := (Functor.LaxBraided.ofNatIso e).braided }⟩⟩

/-- Arbitrary scheme inverse image preserves lisse (dualizable) condensed complexes.
Source: HRS Definition 3.3 and the Section 3 pullback paragraph
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG step 2): apply the strong symmetric monoidal functor of step 1 to a dual,
its evaluation and its coevaluation. Compose with the invertible tensor and unit
comparisons. Their coherence transports both triangle identities, so the image is dualizable. -/
theorem condensed_derivedPullback_preserves_dualizable
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    Nonempty (HasRightDual K) →
      Nonempty (HasRightDual ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K)) := by
  classical
  obtain ⟨h⟩ := (condensed_derivedPullback_exact_symmetricMonoidal Λ f).2
  let := h
  rintro ⟨hK⟩
  let := hK
  exact ⟨{ rightDual := (CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj Kᘁ
           exact := ExactPairing.map (CondensedRing.upperStar Λ.X f).mapDerivedCategory K Kᘁ }⟩

attribute [local irreducible] Mod.monoidalClosed
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] sheafBraidedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] sheafSymmetricCategory sheafBraidedCategory
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory SymmetricCategory.ofCurried

-- The derived-category isomorphisms in the pullback branch need extra unification.
/-- A single morphism tests dualizability before and after every weakly etale pullback.

Choose a K-flat resolution P of K and the generic DualizabilityDatum for P. Its map χ
models [P,1] ⊗ P → [P,P]. Weakly etale abelian pullback has an exact left adjoint:
left Kan extension over the discrete set of lifts, then sheafification. The ordinary
closed comparison gives its projection formula, which lifts the adjunction to modules.
Coefficient transport is an exact equivalence. Thus the lifted left adjoint is exact,
and pullback preserves K-injectives. The native module closed comparison and preservation
of flat modules let DualizabilityDatum.map use the same χ after pullback. The two generic
criteria identify dualizability with invertibility of Q(χ) and its image.
Source: HRS Lemma 4.5, proof, and the source-library DualizableTransfer construction.
(blueprint: lem-zl-condensed-lisse-proetale-locality). -/
private theorem condensed_dualizability_test
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    ∃ (M N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
      (a : M ⟶ N), (IsDualizable K ↔ IsIso a) ∧
      ∀ {T : Scheme.{u}} (f : T ⟶ X) [WeaklyEtale f],
        IsDualizable ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K) ↔
          IsIso ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.map a) := by
  classical
  -- Cache tensor coherence so later specializations do not repeat instance searches.
  let (Z : Scheme.{u}) : HasColimitsOfSize.{0, 0}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z)) :=
    hasColimitsOfSizeShrink _
  let (Z : Scheme.{u}) (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ.X Z)) : PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft M) := inferInstance
  let (Z : Scheme.{u}) (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ.X Z)) : PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorRight M) := inferInstance
  let (Z : Scheme.{u}) (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z))) :
      GradedObject.HasTensor₄ObjExt A B C D := inferInstance
  let (Z : Scheme.{u}) (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z))) :
      GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance
  let (Z : Scheme.{u}) (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z))) :
      GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance
  let : HasZeroObject (ObjectProperty.flat
      (A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ.X X))).FullSubcategory := inferInstance
  let : HasFiniteCoproducts (ObjectProperty.flat
      (A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ.X X))).FullSubcategory := inferInstance
  let : IsIdempotentComplete (ObjectProperty.flat
      (A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ.X X))).FullSubcategory := inferInstance
  obtain ⟨R₀⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
  obtain ⟨R, hR⟩ : ∃ R : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)),
      R.F.PreservesZeroMorphisms := ⟨R₀.reduced, inferInstance⟩
  let := hR
  have hι := (ObjectProperty.flat
    (A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))).essImage_ι_le
  let K₀ := DerivedCategory.Q.objPreimage K
  let P := R.resolutionFunctor.obj K₀
  have : IsIso (DerivedCategory.Q.map (R.resolutionNatTrans.app K₀)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e : K ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (R.resolutionNatTrans.app K₀))).symm
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).2
    (R.kFlat_resolutionFunctor_obj hι K₀)
  obtain ⟨d⟩ := DerivedCategory.DualizabilityDatum.nonempty P hP
  refine ⟨_, _, DerivedCategory.Q.map d.χ, ?_, fun {T} f _ ↦ ?_⟩
  · rw [DerivedCategory.isIso_Q_map_iff_quasiIso, ← d.isDualizable_Q_obj_iff hP]
    exact ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩
  · let : HasColimitsOfSize.{0, 0}
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)) :=
      hasColimitsOfSizeShrink _
    let S := upperStar Ab.{u + 1} f
    let : MonObj (condensedRingObj Λ.X X) := inferInstance
    let : S.Additive := additive_upperStar Ab.{u + 1} f
    let : S.Monoidal := by dsimp only [S]; infer_instance
    let L := Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) Ab.{u + 1}
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology X)
    let adj : L ⊣ S :=
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) Ab.{u + 1}
        (Scheme.ProEt.topology T) (Scheme.ProEt.topology X)).ofNatIsoRight
        (upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).symm
    have : PreservesFiniteLimits L := by
      have := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian
        Ab.{u + 1} (P := @WeaklyEtale) (inferInstance : WeaklyEtale f)
      exact comp_preservesFiniteLimits (sheafToPresheaf _ _)
        (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op.lan) ⋙
          presheafToSheaf _ _)
    have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
    have := Adjunction.left_adjoint_additive adj
    have (A : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
        IsIso (Functor.LaxMonoidal.ihomComparison S A) :=
      isIso_ihomComparison_upperStar Ab.{u + 1} f A
    let : adj.HasProjectionFormula := ⟨fun A B ↦ by
      have := Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison adj A
      change IsIso (adj.projectionFormulaMap A B)
      rw [Adjunction.projectionFormulaMap, Adjunction.homEquiv_counit]
      exact inferInstanceAs (IsIso ((Functor.Monoidal.projectionMap adj A).app B))⟩
    let G := CondensedRing.supportPullback Λ.X f
    let : G.Additive := CondensedRing.supportPullback_additive Λ.X f
    let : G.Monoidal := CondensedRing.supportPullback_monoidal Λ.X f
    let : PreservesFiniteLimits G := CondensedRing.supportPullback_leftExact Λ.X f
    let : PreservesFiniteColimits G := CondensedRing.supportPullback_rightExact Λ.X f
    let LM : CondensedRing.supportModules Λ.X T ⥤ CondensedRing.supportModules Λ.X X :=
      (CondensedRing.supportCoefficientEquivalence Λ.X f).inverse ⋙
        adj.mapModLeft (condensedRingObj Λ.X X)
    let aG : LM ⊣ G :=
      (CondensedRing.supportCoefficientEquivalence Λ.X f).symm.toAdjunction.comp
        (adj.mapModLeftAdjunction (B := condensedRingObj Λ.X X))
    have : PreservesColimitsOfSize.{0, 0} LM := aG.leftAdjoint_preservesColimits
    have := Adjunction.left_adjoint_additive aG
    have : PreservesFiniteLimits LM := by
      dsimp only [LM]
      exact comp_preservesFiniteLimits _ _
    have (A : CondensedRing.supportModules Λ.X X) :
        IsIso (Functor.LaxMonoidal.ihomComparison G A) :=
      CondensedRing.supportPullback_ihomComparison_isIso Λ.X f A
    have : G.PreservesFlat := inverseImageModule_preservesFlat f
      (condensedRingObj Λ.X X) (condensedRingObj Λ.X T)
      (asIso (condensedPullbackHom Λ.X f)).inv
    have : PreservesColimitsOfSize.{0, 0} G :=
      (CondensedRing.supportPullbackAdjunction Λ.X f).leftAdjoint_preservesColimits
    have hGP : (HomotopyCategory.quasiIso
        (CondensedRing.supportModules Λ.X T) (.up ℤ)).kFlat
        ((HomotopyCategory.quotient (CondensedRing.supportModules Λ.X T) (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj P)) := by
      apply (HomotopyCategory.kFlat_quotient_obj_iff _).2
      exact G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj R hι K₀
    let eF : (CondensedRing.upperStar Λ.X f) ≅ G :=
      Functor.isoWhiskerLeft
        ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f))
    let eG := Functor.mapDerivedCategoryNatIso eF
    let eQ := G.mapDerivedCategoryFactors
    refine Iff.trans ?_ (NatIso.isIso_map_iff eG (DerivedCategory.Q.map d.χ)).symm
    refine Iff.trans ?_ (NatIso.isIso_map_iff eQ d.χ).symm
    rw [Functor.comp_map, DerivedCategory.isIso_Q_map_iff_quasiIso,
      ← d.isDualizable_Q_obj_map_iff G aG hGP]
    let e' := eG.app K ≪≫ G.mapDerivedCategory.mapIso e ≪≫ eQ.app P
    exact ⟨fun h ↦ h.of_iso e', fun h ↦ h.of_iso e'.symm⟩

/-- Dualizability is local for every pro-etale covering family, including empty and
infinite families. The index universe is independent of the universe of schemes.
Source: HRS Definition 3.3 and Lemma 4.5, lisse assertion
(blueprint: lem-zl-condensed-lisse-proetale-locality).

Proof (DAG step 4): the forward direction is monoidal preservation of a dual.
For the converse use condensed_dualizability_test: one derived morphism a is invertible
exactly when K is dualizable, and every weakly etale inverse image of a is invertible
exactly when the corresponding inverse image of K is dualizable. The private helper
constructs a using K-flat and K-injective resolutions and proves these equivalences with
the generic chain-level dualizability criterion. Joint conservativity from
lem-zl-condensed-cover-restriction-conservative detects invertibility of a. This works
for every cover, including an empty or infinite family. -/
theorem condensed_dualizable_iff_proetale_cover
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    Nonempty (HasRightDual K) ↔
      ∀ i : 𝒰.I₀, Nonempty
        (HasRightDual ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) := by
  constructor
  · intro h i
    exact condensed_derivedPullback_preserves_dualizable Λ (𝒰.f i) K h
  · intro h
    obtain ⟨M, N, a, hK, ha⟩ := condensed_dualizability_test Λ X K
    apply hK.mpr
    apply ((condensed_cover_restriction_conservative Λ X 𝒰).1 M N a).mpr
    intro i
    have : WeaklyEtale (𝒰.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
    exact (ha (𝒰.f i)).mp (h i)

end AlgebraicGeometry.ProEtale
