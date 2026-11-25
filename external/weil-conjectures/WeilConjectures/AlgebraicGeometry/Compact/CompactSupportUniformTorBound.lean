/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleUnitLerayChainFormula
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence

/-!
# Uniform Tor bounds for compact supports

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
`sk-lem-sp-tower-bound-uniform.md`; Stacks Project, Tag 0F10
(blueprint: prose-09-23).

Finite coefficients use the recorded ordinary ringed pro-etale derived category.
The second clause uses the existing strict semilinear sequence-site presentation of
coefficient towers. Its natural index n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Etale.derivedTensor

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem comparison_tor (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (a b : ℤ) (hab : a ≤ b)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K ↔
      HasProEtaleTorAmplitude T A
        ((finiteCoefficientIntrinsicDerivedComparison T A).obj K) a b := by
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let R := finiteCoefficientIntrinsicRealization T A
  let e := (Functor.mapDerivedCategoryCompIso C R).symm.app K
  have h := comparison_torAmplitudeIn_iff A T a b hab ⟨K, hK⟩
  exact h.trans ⟨fun h ↦ tor_of_iso T A e.symm h, fun h ↦ tor_of_iso T A e h⟩

private noncomputable def open_coordinates (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    proEtaleRingDerivedOpenExtension j (proEtaleConstantRing Z A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A) ≅
      sfIntrinsicDerivedOpen A j := by
  let a := Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback A j)
  let b := (sfIntrinsicOpenAdjunction A j).ofNatIsoRight
    (openSquarePullbackModel A j).symm
  exact Functor.mapDerivedCategoryNatIso (a.leftAdjointUniq b)

private noncomputable def push_coordinates (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) ≅
      proEtaleConstantDerivedDirectImage f A :=
  Functor.rightDerivedFunctorNatIso (proEtaleUnitLerayDirectImageIso A f)

private noncomputable def compact_coordinates (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) [QuasiCompact c.i] :
    proEtaleRingCompactSupportImage c (proEtaleConstantRing Y A)
        (proEtaleConstantRing c.Z A) (proEtaleConstantRing X A)
        (proEtaleConstantRingComparison c.g A) (proEtaleConstantRingComparison c.i A) ≅
      sfIntrinsicDerivedOpen A c.i ⋙ proEtaleConstantDerivedDirectImage c.g A :=
  Functor.isoWhiskerRight (open_coordinates A c.i) _ ≪≫
    Functor.isoWhiskerLeft _ (push_coordinates A c.g)

private noncomputable def compact_comparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A Y).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj K.obj) ≅
      (proEtaleConstantDerivedDirectImage c.g A).obj
        ((sfIntrinsicDerivedOpen A c.i).obj ((etaleOriginOpenComparison A X).obj K.obj)) := by
  let j := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  exact (etaleOriginOpenComparison A Y).mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor.mapIso
        (j.mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    etaleOriginOpenDirectImageComparison A c.g (j.mapDerivedCategoryPlus.obj K) ≪≫
    (proEtaleConstantDerivedDirectImage c.g A).mapIso
      ((etaleOriginOpenComparison A c.Z).mapIso (j.mapDerivedCategoryPlusCompatibility.app K) ≪≫
        (etaleOriginOpenExtensionComparison A c.i).app K.obj)

private theorem etale_tor (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasInvertibleExponent Λ Y] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (K : Etale.DerivedCategoryModule Λ X)
    (ht : Etale.DerivedCategory.hasTorAmplitudeIn Λ X a b K) :
    Etale.DerivedCategory.hasTorAmplitudeIn Λ Y a (b + 2 * (d : ℤ))
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  intro N q hq
  let B := ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj N))
  have hgeB : B.IsGE a := (DerivedCategory.isGE_iff B a).mpr
    (fun i hi ↦ ht _ i (.inl hi))
  have hleB : B.IsLE b := (DerivedCategory.isLE_iff B b).mpr
    (fun i hi ↦ ht _ i (.inr hi))
  have hbB : DerivedCategory.TStructure.t.bounded B := ⟨⟨a, hgeB⟩, ⟨b, hleB⟩⟩
  let H := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f
  have hge : (H.obj B).IsGE a := Etale.isGE_rightDerivedLowerShriek_obj Λ f B hbB a
  have hsheaf (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (H.obj ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE (2 * (d : ℤ)) := by
    apply (DerivedCategory.isLE_iff _ _).mpr
    intro q hq
    let Fplus := (DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
    have hz := Etale.isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE
      k Λ X Y f d hd F q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ
        (Etale.compactSupportAmplitudeCompactification k Y f)
        (HasCompactification.compactification f)).app Fplus)).symm
  have hle : (H.obj B).IsLE (b + 2 * (d : ℤ)) :=
    DerivedCategory.isLE_obj_of_isLE H (2 * (d : ℤ)) hsheaf B hbB b
  obtain ⟨e⟩ := Etale.nonempty_iso_tensor_singleFunctor_obj_rightDerivedLowerShriek Λ f K N
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ q).mapIso e)
  rcases hq with hq | hq
  · exact (DerivedCategory.isGE_iff (H.obj B) a).mp hge q hq
  · exact (DerivedCategory.isLE_iff (H.obj B) (b + 2 * (d : ℤ))).mp hle q hq

private theorem etale_bounded_iff (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private noncomputable def comparison_coordinates (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) :
    finiteCoefficientIntrinsicDerivedComparison T A ≅ etaleOriginOpenComparison A T :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T)
    (finiteCoefficientIntrinsicRealization T A)).symm

private theorem finite_bound (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Finite A]
    [HasInvertibleExponent (ULift.{u + 1, u} A) (Spec (.of k))]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (hab : a ≤ b) (M : proEtaleDerivedCategory X A)
    (hM : spFiniteConstructibleTor X A M) (ht : HasProEtaleTorAmplitude X A M a b) :
    let H := proEtaleRingCompactSupportImage c
      (proEtaleConstantRing Y A) (proEtaleConstantRing c.Z A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison c.g A)
      (proEtaleConstantRingComparison c.i A)
    spFiniteConstructibleTor Y A (H.obj M) ∧
      HasProEtaleTorAmplitude Y A (H.obj M) a (b + 2 * (d : ℤ)) ∧
      ∀ q : ℤ, (q < a ∨ b + 2 * (d : ℤ) < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj (H.obj M)) := by
  let Λ := ULift.{u + 1, u} A
  have : HasCompactification f := c.hasCompactification
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (X ↘ Spec (.of k))
  have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
  obtain ⟨K, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin X A).2.2.1 M |>.mpr
    ⟨hM.2.1, hM.1⟩
  have hKb := (etale_bounded_iff X Λ K.obj).mp K.property
  let Kplus : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨K.obj, hKb.1.1⟩
  have hKt := (comparison_tor X A a b hab K.obj hKb.1.1).mpr
    (tor_of_iso X A e.symm ht)
  let L := (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K.obj
  have hLb := Etale.boundedConstructible_rightDerivedLowerShriek Λ f
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (comp_over f _) K.obj hKb
  have hLt := etale_tor k Λ X Y f d hd a b K.obj hKt
  have hLP := (etale_bounded_iff Y Λ L).mpr hLb
  let H := proEtaleRingCompactSupportImage c
    (proEtaleConstantRing Y A) (proEtaleConstantRing c.Z A)
    (proEtaleConstantRing X A) (proEtaleConstantRingComparison c.g A)
    (proEtaleConstantRingComparison c.i A)
  let ei : (etaleOriginOpenComparison A X).obj K.obj ≅ M :=
    (comparison_coordinates A X).symm.app K.obj ≪≫ e
  let ec := (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ
    (HasCompactification.compactification f) c).app Kplus
  let eo : (finiteCoefficientIntrinsicDerivedComparison Y A).obj L ≅ H.obj M :=
    (comparison_coordinates A Y).app L ≪≫
      (etaleOriginOpenComparison A Y).mapIso ec ≪≫ compact_comparison A c Kplus ≪≫
      (sfIntrinsicDerivedOpen A c.i ⋙ proEtaleConstantDerivedDirectImage c.g A).mapIso ei ≪≫
      (compact_coordinates A c).symm.app M
  have hbc := (finiteRing_constructibleDerived_origin Y A).2.2.1 (H.obj M) |>.mp
    ⟨⟨L, hLP⟩, ⟨eo⟩⟩
  have hab' : a ≤ b + 2 * (d : ℤ) := by omega
  have hto := tor_of_iso Y A eo
    ((comparison_tor Y A a (b + 2 * (d : ℤ)) hab' L hLb.1.1).mp hLt)
  refine ⟨⟨hbc.2, hbc.1, a, b + 2 * (d : ℤ), hto⟩, hto, ?_⟩
  have hcon := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hLt)
  have hv : ∀ q : ℤ, q < a ∨ b + 2 * (d : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
    intro q hq
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff L a).mp hcon.1 q hq
    · exact (DerivedCategory.isLE_iff L (b + 2 * (d : ℤ))).mp hcon.2 q hq
  have hv' := ((finiteRing_constructibleDerived_origin Y A).2.2.2 L a
    (b + 2 * (d : ℤ))).mp hv
  intro q hq
  exact (hv' q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso eo).symm

end AlgebraicGeometry.ProEtale
