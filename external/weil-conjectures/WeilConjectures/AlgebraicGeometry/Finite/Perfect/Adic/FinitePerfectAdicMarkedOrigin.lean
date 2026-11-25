/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceDerivedCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.InternalHom

/-! # Retained etale origin of a marked finite quotient

Source: Stacks Project, Tags 09AL, 09B1 and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Fixed finite-scalar coordinates of the actual quotient on the chart.
Source: Stacks Tags 03CY, 099R and 09AL.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-origin). -/
def finitePerfectAdicQuotientCoordinates
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (n : ℕ) :=
  (finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
    (completedAdicFiniteCommRing X d n) (φ n) V).mapDerivedCategory.obj
      ((completedAdicQuotientReduction X d n).obj M)

/-- Restriction to nested charts commutes with the fixed coefficient encoding. -/
private def chartPullbackIso
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) {V W : X.Etale} (g : W ⟶ V) :
    finiteCoefficientSliceRestriction X B R ψ V ⋙
        AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) g.left ≅
      finiteCoefficientSliceRestriction X B R ψ W := by
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let H := SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ) ⋙
    proEtaleModuleRestriction X B
  change H ⋙ (AlgebraicGeometry.ProEtale.localizationRestriction D V.hom inferInstance ⋙
    AlgebraicGeometry.ProEtale.upperStar D g.left) ≅
      H ⋙ AlgebraicGeometry.ProEtale.localizationRestriction D W.hom inferInstance
  apply Functor.isoWhiskerLeft H
  exact Functor.isoWhiskerRight
      (AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction D V.hom
        inferInstance).symm _ ≪≫
    (AlgebraicGeometry.ProEtale.upperStarComp D g.left V.hom).symm ≪≫
    AlgebraicGeometry.ProEtale.upperStarCongr D (MorphismProperty.Over.w g) ≪≫
    AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction D W.hom inferInstance

private def chartDerivedRestriction
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) (V : X.Etale) :
    DerivedCategory (SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ⥤
      DerivedCategory (Sheaf (ProEt.topology V.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} B))) :=
  have := (finiteCoefficientSliceRestriction_exact X B R ψ V).1
  have := (finiteCoefficientSliceRestriction_exact X B R ψ V).2.1
  have := (finiteCoefficientSliceRestriction_exact X B R ψ V).2.2
  (finiteCoefficientSliceRestriction X B R ψ V).mapDerivedCategory

private def derivedChartPullbackIso
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) {V W : X.Etale} (g : W ⟶ V)
    (K : DerivedCategory (SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))) :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
      g.left).mapDerivedCategory.obj ((chartDerivedRestriction X B R ψ V).obj K) ≅
      (chartDerivedRestriction X B R ψ W).obj K := by
  have := (finiteCoefficientSliceRestriction_exact X B R ψ V).1
  have := (finiteCoefficientSliceRestriction_exact X B R ψ V).2.1
  have := (finiteCoefficientSliceRestriction_exact X B R ψ V).2.2
  have := (finiteCoefficientSliceRestriction_exact X B R ψ W).1
  have := (finiteCoefficientSliceRestriction_exact X B R ψ W).2.1
  have := (finiteCoefficientSliceRestriction_exact X B R ψ W).2.2
  change (AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} B)) g.left).mapDerivedCategory.obj
        ((finiteCoefficientSliceRestriction X B R ψ V).mapDerivedCategory.obj K) ≅
      (finiteCoefficientSliceRestriction X B R ψ W).mapDerivedCategory.obj K
  exact (Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
      (Functor.mapDerivedCategoryNatIso (chartPullbackIso X B R ψ g)).app K

/-- The coefficient lift is exact; it changes only the universe of the underlying module. -/
private theorem chartAlgebraLift_exact (B : Type t) [CommRing B] :
    let S := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
    PreservesFiniteLimits S ∧ PreservesFiniteColimits S := by
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  exact ⟨inferInstance, inferInstance⟩

/-- A marked finite quotient descends with its actual comparison retained.
No consecutive arrow or completed-scalar realization is asserted.

Source: Stacks Project, Tags 09AL and 09B1, applied as in Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-marked-origin).

Proof: encode the quotient in fixed finite scalars on the chart. The marking cover
identifies its cohomology with constants on the finite homology modules of the
perfect model, and bounds it in the model's cohomological interval. Descent of finite
locally constant sheaves gives etale origins of these cohomology sheaves. Bounded
truncation induction then gives an etale origin and a retained isomorphism. Exact
faithful comparison reflects the bounds. Its full faithfulness on sheaves identifies
the homology of the etale origin with the finite locally constant origins already
constructed. Pull the retained comparison to a member of the marking cover and lift
its local isomorphism through the bounded-below comparison adjunction. Compatibility
of constant sheaves with pullback gives a section of the derived Isom presheaf.
Every separably closed geometric point lifts to this etale cover; sheafification and
the corresponding presheaf-fiber map give the asserted inhabited Isom stalk.
Empty charts and zero coefficient rings obey the same argument. -/
theorem finitePerfectAdic_marked_origin
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) (n : ℕ)
    (hp : DerivedCategory.IsPerfect (T.level n)) :
    ∃ K : DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))),
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      (∀ i : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      Nonempty (((ProEtale.comparisonUpperStar
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj K ≅
        finitePerfectAdicQuotientCoordinates X d φ M V n) ∧
      (∀ (Ω : Type t) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ V.left),
        Nonempty ((pointSmallEtale x).sheafFiber.obj
          (derivedLocalIsomorphismSheaf (finitePerfectAdicEtaleConstant V.left T n) K))) := by
  classical
  let B := A ⧸ d.ideal ^ (n + 1)
  let : Finite B := d.quotientFinite n
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let S := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  have := (chartAlgebraLift_exact B).1
  have := (chartAlgebraLift_exact B).2
  let R := completedAdicFiniteCommRing X d n
  let Q := (completedAdicQuotientReduction X d n).obj M
  let J := finitePerfectAdicQuotientCoordinates X d φ M V n
  obtain ⟨T', hT', ht⟩ := hmark n
  have hx (x : V.left) : ∃ (W : X.Etale) (g : W ⟶ V),
      T' g ∧ ∃ w : W.left, g.left w = x :=
    (mem_smallEtaleTopology_iff T').mp hT' x
  choose W g hg w hw using hx
  let E := (finitePerfectAdicAlgebraLift B).obj (T.level n)
  let CQ (x : V.left) := constantSheaf (ProEt.topology (W x).left) D
  let N (i : ℤ) := S.obj ((DerivedCategory.homologyFunctor _ i).obj (T.level n))
  have eJ (x : V.left) :
      (ProEtale.upperStar D (g x).left).mapDerivedCategory.obj J ≅
        (CQ x).mapDerivedCategory.obj E :=
    derivedChartPullbackIso X B R (φ n) (g x) Q ≪≫
      ((finiteCoefficient_slice_derived_coordinates X B R (φ n) (hφ n) (W x)).1 _ _
        |>.mp (ht (W x) (g x) (hg x))).some ≪≫
      ((finiteCoefficient_slice_derived_coordinates X B R (φ n) (hφ n) (W x)).2 _).some
  let eh (x : V.left) (i : ℤ) :
      (ProEtale.upperStar D (g x).left).obj
        ((DerivedCategory.homologyFunctor _ i).obj J) ≅ (CQ x).obj (N i) :=
    ((ProEtale.upperStar D (g x).left).mapDerivedCategoryHomologyFunctorIso i).app J ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (eJ x) ≪≫
      (((CQ x).mapDerivedCategoryHomologyFunctorIso i).app E).symm ≪≫
      (CQ x).mapIso ((S.mapDerivedCategoryHomologyFunctorIso i).app (T.level n)).symm
  have hN (i : ℤ) : Finite (N i) := by
    have := hp.finite_homology i
    have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) i).obj
        (T.level n)) := Module.finite_of_finite B
    exact inferInstanceAs (Finite (ULift.{t + 1}
      ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) i).obj (T.level n))))
  have hcover : Presieve.ofArrows (fun x ↦ (W x).left) (fun x ↦ (g x).left) ∈
      proetalePrecoverage V.left := by
    apply etalePrecoverage_le_proetalePrecoverage
    exact (ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨x, w x, hw x⟩, fun _ ↦ inferInstance⟩
  obtain ⟨a, b, ha, hb⟩ := hp.exists_homologyConcentratedIn
  have hzero (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj J) := by
    have hz : IsZero (N i) := by
      apply S.map_isZero
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff _ a).mp ha i hi
      · exact (DerivedCategory.isLE_iff _ b).mp hb i hi
    have : IsIso (0 : (DerivedCategory.homologyFunctor _ i).obj J ⟶ 0) := by
      apply ProEtale.isIso_of_isIso_localizationRestriction D _
        (fun x ↦ (g x).left) hcover
      intro x
      let F := ProEtale.localizationRestriction D (g x).left inferInstance
      have : F.Additive := { map_add := rfl }
      have hz' : IsZero (F.obj ((DerivedCategory.homologyFunctor _ i).obj J)) :=
        (((CQ x).map_isZero hz).of_iso (eh x i)).of_iso
          ((ProEtale.upperStarIsoLocalizationRestriction D (g x).left inferInstance).app _).symm
      exact isIso_of_source_target_iso_zero _ hz'.isoZero
        (F.map_isZero (isZero_zero _)).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : (DerivedCategory.homologyFunctor _ i).obj J ⟶ 0))
  have heart (i : ℤ) := etale_origin_of_finite_models V.left (ULift.{t + 1} B)
    ((DerivedCategory.homologyFunctor _ i).obj J)
    ⟨ULift.{t + 1} V.left, fun x ↦ (W x.down).left, fun x ↦ (g x.down).left,
      (by
        apply etalePrecoverage_le_proetalePrecoverage
        exact (ofArrows_mem_precoverage_iff _).mpr
          ⟨fun x ↦ ⟨⟨x⟩, w x, hw x⟩, fun _ ↦ inferInstance⟩),
      fun x ↦ ⟨N i, hN i, ⟨eh x.down i⟩⟩⟩
  choose G hG eG using heart
  have hJbound : DerivedCategory.TStructure.t.bounded J :=
    ⟨⟨a, (DerivedCategory.isGE_iff J a).2 (fun i hi ↦ hzero i (Or.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff J b).2 (fun i hi ↦ hzero i (Or.inr hi))⟩⟩
  let C := ProEtale.comparisonUpperStar D V.left
  obtain ⟨K, hKplus, ⟨eK⟩⟩ :=
    ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology
      (ULift.{t + 1} B) V.left (fun i ↦ ⟨G i, eG i⟩) hJbound
  refine ⟨K, ⟨a, b, ?_⟩, ?_, ⟨eK⟩, ?_⟩
  · intro i hi
    exact C.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((hzero i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eK))
  · intro i
    let e : C.obj ((DerivedCategory.homologyFunctor _ i).obj K) ≅ C.obj (G i) :=
      (C.mapDerivedCategoryHomologyFunctorIso i).app K ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso eK ≪≫ (eG i).some.symm
    exact IsFiniteLocallyConstantSheaf.of_iso (C.preimageIso e).symm
  · intro Ω _ _ x
    let 𝒰 : Cover.{t} etalePrecoverage V.left :=
      Cover.mkOfCovers V.left (fun z ↦ (W z).left) (fun z ↦ (g z).left)
        (fun z ↦ ⟨z, w z, hw z⟩) (fun _ ↦ inferInstance)
    obtain ⟨i, y, hy⟩ := 𝒰.exists_comp_eq_of_isSepClosed x
    let U := Etale.mk (g i).left
    let F := AlgebraicGeometry.Etale.upperStar D (g i).left
    let F' := ProEtale.upperStar D (g i).left
    let C' := ProEtale.comparisonUpperStar D (W i).left
    let EC := constantSheaf (W i).left.smallEtaleTopology D
    let PC := constantSheaf (ProEt.topology (W i).left) D
    let e₁ : C'.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅
        PC.mapDerivedCategory.obj E :=
      (Functor.mapDerivedCategoryCompIso F C').app K ≪≫
        (Functor.mapDerivedCategoryNatIso
          (ProEtale.comparisonUpperStarUpperStarIso D (g i).left).symm).app K ≪≫
        ((Functor.mapDerivedCategoryCompIso C F').app K).symm ≪≫
        F'.mapDerivedCategory.mapIso eK ≪≫ eJ i
    let e₂ : C'.mapDerivedCategory.obj (EC.mapDerivedCategory.obj E) ≅
        PC.mapDerivedCategory.obj E :=
      (Functor.mapDerivedCategoryCompIso EC C').app E ≪≫
        (Functor.mapDerivedCategoryNatIso
          (ProEtale.constantSheafCompComparisonUpperStarIso D (W i).left)).app E
    have hKbound : DerivedCategory.TStructure.t.bounded K :=
      C.bounded_of_bounded_mapDerivedCategory_obj
        (DerivedCategory.TStructure.t.bounded.prop_of_iso eK.symm hJbound)
    have hEbound : DerivedCategory.TStructure.t.bounded E :=
      S.bounded_mapDerivedCategory_obj hp.bounded
    have h₁ := F.bounded_mapDerivedCategory_obj hKbound
    have h₂ := EC.bounded_mapDerivedCategory_obj hEbound
    have := ProEtale.isIso_derivedComparisonAdjunction_unit_app D (W i).left _ h₁.1
    have := ProEtale.isIso_derivedComparisonAdjunction_unit_app D (W i).left _ h₂.1
    let e : F.mapDerivedCategory.obj K ≅ EC.mapDerivedCategory.obj E :=
      asIso ((ProEtale.derivedComparisonAdjunction D (W i).left).unit.app _) ≪≫
        (ProEtale.comparisonLowerStar D (W i).left).rightDerivedFunctor.mapIso
          (e₁ ≪≫ e₂.symm) ≪≫
        (asIso ((ProEtale.derivedComparisonAdjunction D (W i).left).unit.app _)).symm
    let eC : (localIsomorphismRestriction V.left (ULift.{t + 1} B) U).obj
        (finitePerfectAdicEtaleConstant V.left T n) ≅ EC.mapDerivedCategory.obj E :=
      (Functor.mapDerivedCategoryCompIso _ _).app E ≪≫
        (Functor.mapDerivedCategoryNatIso (upperStarConstantSheafIso D (g i).left)).app E
    let P := derivedLocalIsomorphismPresheaf
      (finitePerfectAdicEtaleConstant V.left T n) K
    let H := derivedLocalIsomorphismSheaf (finitePerfectAdicEtaleConstant V.left T n) K
    let z : H.obj.obj (op U) := (toSheafify V.left.smallEtaleTopology P).app (op U)
      (eC ≪≫ e.symm)
    exact ⟨(pointSmallEtale x).toPresheafFiber U (Over.homMk y hy) H.obj z⟩

end AlgebraicGeometry.Scheme
