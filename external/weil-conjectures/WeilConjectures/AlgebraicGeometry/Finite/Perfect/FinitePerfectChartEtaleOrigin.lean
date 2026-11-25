/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceDerivedCoordinates
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
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
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-! # Etale origin and reflection of local constant models

Source: Stacks Project, Tags 09AL, 09B1, 094T and 0951.
(blueprint: lem-weil-pbc-finite-perfect-chart-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

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

set_option linter.unusedVariables false in
/-- A complex over a constant finite ring, on a localized pro-etale site, with uniformly
bounded perfect constant models on an etale covering has etale origin. Constant models
of this origin are exactly the constant models of the original complex. This assertion
only constructs the origin and compares its local models: it does not assert boundedness,
local constancy of its cohomology, or perfectness of a geometric fibre.

Source: Stacks Project, proetale.tex, lemma-compare-constructible-derived (09AL),
lemma-compare-locally-constant (09B1), and weakly etale localization (094T, 0951).
(blueprint: lem-weil-pbc-finite-perfect-chart-etale-origin).

Proof: identify the slice at V with the pro-etale site of V.left. Transport the ring
along the specified coefficient isomorphism psi, which identifies its restriction with
the constant B ring. Termwise constant realization commutes with this transport. The
local models show that every cohomology sheaf is etale locally a constant finite module:
B is finite, so homology of the given finite-projective complex is finite. Its cohomology
vanishes outside [a,b]. Descent for finite locally constant sheaves therefore identifies
each cohomology sheaf with the inverse image of an etale sheaf. Bounded truncation
induction, lifting connecting morphisms by full faithfulness of derived inverse image,
produces L (09AL). On any further etale chart W the same site and coefficient
identifications commute with restriction. Exact inverse image takes constant L-models
to the displayed constant K-models. Conversely the model isomorphism makes both sides
bounded below; full faithfulness of derived inverse image lifts it and its inverse.
This works for every algebraic F, including unbounded F: if its constant realization
is isomorphic to the bounded restriction of K, exact faithful inverse image reflects
boundedness of that sheaf complex. Empty charts cause no exception, since both sheaf
categories there are zero. No neighbouring coefficient levels or adic completion enter. -/
theorem finitePerfectChart_etale_origin
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) (hψ : IsIso ψ)
    (K : DerivedCategory (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)))
    (V : X.Etale) (a b : ℤ) (hab : a ≤ b)
    (hmodel : ∃ T : Sieve V, T ∈ X.smallEtaleTopology V ∧
      ∀ (W : X.Etale) (g : W ⟶ V), T g →
        ∃ P : CochainComplex (ModuleCat.{t} B) ℤ,
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective B (P.X i) ∧ Module.Finite B (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses
                ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
                ((toProEt X).obj W) K ≅
              ringedSiteDerivedRestrictionOfUniverses
                ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
                ((toProEt X).obj W) ((completedAdicDerivedChange X ψ).obj
                  ((finitePerfectAdicDerivedConstant X B).obj (DerivedCategory.Q.obj P))))) :
    ∃ L : DerivedCategory
        (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B))),
      ∀ (W : X.Etale) (g : W ⟶ V) (F : DerivedCategory (ModuleCat.{t} B)),
        Nonempty
          ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
              g.left).mapDerivedCategory.obj L ≅
            (constantSheaf W.left.smallEtaleTopology
              (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapDerivedCategory.obj
                ((finitePerfectAdicAlgebraLift B).obj F)) ↔
        Nonempty
          (ringedSiteDerivedRestrictionOfUniverses
              ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
              ((toProEt X).obj W) K ≅
            ringedSiteDerivedRestrictionOfUniverses
              ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
              ((toProEt X).obj W) ((completedAdicDerivedChange X ψ).obj
                ((finitePerfectAdicDerivedConstant X B).obj F))) := by
  classical
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let S := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  have := (chartAlgebraLift_exact B).1
  have := (chartAlgebraLift_exact B).2
  let H := finiteCoefficientSliceRestriction X B R ψ V
  let J := H.mapDerivedCategory.obj K
  obtain ⟨T, hT, ht⟩ := hmodel
  have hx (x : V.left) : ∃ (W : X.Etale) (g : W ⟶ V),
      T g ∧ ∃ w : W.left, g.left w = x :=
    (mem_smallEtaleTopology_iff T).mp hT x
  choose W g hg w hw using hx
  choose P ha hb hP eP using fun x ↦ ht (W x) (g x) (hg x)
  have eJ (x : V.left) :
      (AlgebraicGeometry.ProEtale.upperStar D (g x).left).mapDerivedCategory.obj J ≅
        (constantSheaf (ProEt.topology (W x).left) D).mapDerivedCategory.obj
          ((finitePerfectAdicAlgebraLift B).obj (DerivedCategory.Q.obj (P x))) :=
    derivedChartPullbackIso X B R ψ (g x) K ≪≫
      ((finiteCoefficient_slice_derived_coordinates X B R ψ hψ (W x)).1 _ _
        |>.mp (eP x)).some ≪≫
      ((finiteCoefficient_slice_derived_coordinates X B R ψ hψ (W x)).2 _).some
  let CQ (x : V.left) := constantSheaf (ProEt.topology (W x).left) D
  let N (x : V.left) (q : ℤ) :=
    S.obj ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Q.obj (P x)))
  let eh (x : V.left) (q : ℤ) :
      (AlgebraicGeometry.ProEtale.upperStar D (g x).left).obj
        ((DerivedCategory.homologyFunctor _ q).obj J) ≅ (CQ x).obj (N x q) :=
    ((AlgebraicGeometry.ProEtale.upperStar D (g x).left).mapDerivedCategoryHomologyFunctorIso q).app
      J ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso (eJ x) ≪≫
    (((CQ x).mapDerivedCategoryHomologyFunctorIso q).app
      (S.mapDerivedCategory.obj (DerivedCategory.Q.obj (P x)))).symm ≪≫
    (CQ x).mapIso ((S.mapDerivedCategoryHomologyFunctorIso q).app
      (DerivedCategory.Q.obj (P x))).symm
  have hN (x : V.left) (q : ℤ) : Finite (N x q) := by
    have hp : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P x)) :=
      ⟨P x, a, b, ha x, hb x, hP x, ⟨Iso.refl _⟩⟩
    have := hp.finite_homology q
    have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) q).obj
      (DerivedCategory.Q.obj (P x))) := Module.finite_of_finite B
    exact inferInstanceAs (Finite (ULift.{t + 1}
      ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) q).obj
        (DerivedCategory.Q.obj (P x)))))
  have hcover : Presieve.ofArrows (fun x ↦ (W x).left) (fun x ↦ (g x).left) ∈
      proetalePrecoverage V.left := by
    apply etalePrecoverage_le_proetalePrecoverage
    exact (ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨x, w x, hw x⟩, fun _ ↦ inferInstance⟩
  have hzero (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj J) := by
    have hz (x : V.left) : IsZero ((CQ x).obj (N x q)) := by
      apply (CQ x).map_isZero
      apply S.map_isZero
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq
      · exact DerivedCategory.isZero_of_isLE _ b q hq
    have : IsIso (0 : (DerivedCategory.homologyFunctor _ q).obj J ⟶ 0) := by
      apply AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction D _
        (fun x ↦ (g x).left) hcover
      intro x
      let L := AlgebraicGeometry.ProEtale.localizationRestriction D (g x).left inferInstance
      have : L.Additive := { map_add := rfl }
      have hz' : IsZero (L.obj ((DerivedCategory.homologyFunctor _ q).obj J)) :=
        ((hz x).of_iso (eh x q)).of_iso
          ((AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction D
            (g x).left inferInstance).app _).symm
      exact isIso_of_source_target_iso_zero _ hz'.isoZero
        (L.map_isZero (isZero_zero _)).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : (DerivedCategory.homologyFunctor _ q).obj J ⟶ 0))
  have heart (q : ℤ) := etale_origin_of_finite_models V.left (ULift.{t + 1} B)
    ((DerivedCategory.homologyFunctor _ q).obj J)
    ⟨ULift.{t + 1} V.left, fun x ↦ (W x.down).left, fun x ↦ (g x.down).left,
      (by
        apply etalePrecoverage_le_proetalePrecoverage
        exact (ofArrows_mem_precoverage_iff _).mpr
          ⟨fun x ↦ ⟨⟨x⟩, w x, hw x⟩, fun _ ↦ inferInstance⟩),
      fun x ↦ ⟨N x.down q, hN x.down q, ⟨eh x.down q⟩⟩⟩
  choose G hG eG using heart
  have hJbound : DerivedCategory.TStructure.t.bounded J :=
    ⟨⟨a, (DerivedCategory.isGE_iff J a).2 (fun q hq ↦ hzero q (Or.inl hq))⟩,
      ⟨b, (DerivedCategory.isLE_iff J b).2 (fun q hq ↦ hzero q (Or.inr hq))⟩⟩
  let C := AlgebraicGeometry.ProEtale.comparisonUpperStar D V.left
  obtain ⟨L, hLplus, ⟨eL⟩⟩ :=
    AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology
      (ULift.{t + 1} B) V.left (fun q ↦ ⟨G q, eG q⟩) hJbound
  have hLbound : DerivedCategory.TStructure.t.bounded L :=
    C.bounded_of_bounded_mapDerivedCategory_obj
      (DerivedCategory.TStructure.t.bounded.prop_of_iso eL.symm hJbound)
  refine ⟨L, fun Z g F ↦ ?_⟩
  let U := AlgebraicGeometry.Etale.upperStar D g.left
  let U' := AlgebraicGeometry.ProEtale.upperStar D g.left
  let CZ := AlgebraicGeometry.ProEtale.comparisonUpperStar D Z.left
  let EC := constantSheaf Z.left.smallEtaleTopology D
  let PC := constantSheaf (ProEt.topology Z.left) D
  let E := (finitePerfectAdicAlgebraLift B).obj F
  let eZ : CZ.mapDerivedCategory.obj (U.mapDerivedCategory.obj L) ≅
      (finiteCoefficientSliceRestriction X B R ψ Z).mapDerivedCategory.obj K :=
    (Functor.mapDerivedCategoryCompIso U CZ).app L ≪≫
    (Functor.mapDerivedCategoryNatIso
      (AlgebraicGeometry.ProEtale.comparisonUpperStarUpperStarIso D g.left).symm).app L ≪≫
    (Functor.mapDerivedCategoryCompIso C U').symm.app L ≪≫
    U'.mapDerivedCategory.mapIso eL ≪≫ derivedChartPullbackIso X B R ψ g K
  let eC : CZ.mapDerivedCategory.obj (EC.mapDerivedCategory.obj E) ≅
      PC.mapDerivedCategory.obj E :=
    (Functor.mapDerivedCategoryCompIso EC CZ).app E ≪≫
    (Functor.mapDerivedCategoryNatIso
      (AlgebraicGeometry.ProEtale.constantSheafCompComparisonUpperStarIso D Z.left)).app E
  let eF := ((finiteCoefficient_slice_derived_coordinates X B R ψ hψ Z).2 F).some
  constructor
  · rintro ⟨e⟩
    apply ((finiteCoefficient_slice_derived_coordinates X B R ψ hψ Z).1 _ _).mpr
    exact ⟨eZ.symm ≪≫ CZ.mapDerivedCategory.mapIso e ≪≫ eC ≪≫ eF.symm⟩
  · intro e
    let e' := ((finiteCoefficient_slice_derived_coordinates X B R ψ hψ Z).1 _ _).mp e
    let e'' : CZ.mapDerivedCategory.obj (U.mapDerivedCategory.obj L) ≅
        CZ.mapDerivedCategory.obj (EC.mapDerivedCategory.obj E) :=
      eZ ≪≫ e'.some ≪≫ eF ≪≫ eC.symm
    have hb₁ := U.bounded_mapDerivedCategory_obj hLbound
    have hb₂ : DerivedCategory.TStructure.t.bounded (EC.mapDerivedCategory.obj E) :=
      CZ.bounded_of_bounded_mapDerivedCategory_obj
        (DerivedCategory.TStructure.t.bounded.prop_of_iso e''
          (CZ.bounded_mapDerivedCategory_obj hb₁))
    have := AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app
      D Z.left _ hb₁.1
    have := AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app
      D Z.left _ hb₂.1
    exact ⟨asIso ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction D Z.left).unit.app
      (U.mapDerivedCategory.obj L)) ≪≫
      (AlgebraicGeometry.ProEtale.comparisonLowerStar D Z.left).rightDerivedFunctor.mapIso e'' ≪≫
      (asIso ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction D Z.left).unit.app
        (EC.mapDerivedCategory.obj E))).symm⟩

end AlgebraicGeometry.Scheme
