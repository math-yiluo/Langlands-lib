/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor

import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSiteSquare
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-! # Constructible flat models under arbitrary finite scalar extension

Source: Stacks Project, etale-cohomology.tex, Tags 03TT (lemma-when-ctf) and
0GKB (lemma-tensor-constructible), with sites-cohomology.tex, Tags 06YQ, 0G7E,
06YT, 06YY and 08G1 (blueprint: lem-sp-etale-scalar-flat-model).

Scalar extension is the ordinary, uncompleted functor into the B-module derived
category. The ordinary representative retains the target-ring action; its tensor
presentation is B tensor_A P, canonically the symmetric presentation of P tensor_A B.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- A bounded constructible complex of Tor amplitude `[a,b]` has a flat constructible
model in that interval, and every such model computes arbitrary finite scalar extension.
Source: Stacks Project, Tags 03TT and 0GKB
(blueprint: lem-sp-etale-scalar-flat-model).

Proof plan:
1. Apply lem-sf-etale-flat-constructible to T, A, a, b and K. Its forward implication
   supplies the existential model with the specified interval and finite-value strata.
2. Fix any model with these properties. Its upper bound and flatness imply K-flatness
   by lem-pc-bounded-above-flat-kflat-site (06YQ).
3. Apply lem-pur-kflat-change-of-rings (0G7E) to A_T to B_T. Ordinary termwise
   extension has flat B-module terms and is K-flat over B, without assuming B flat
   over A. Its differential is the extended differential; zero terms stay zero.
4. The ordinary etale clauses of lem-sp-constructible-coefficient-site-square
   (0GKB and 03RZ) give constructibility of each extended term and of the cohomology
   of its derived image. On each finite stratum the value M becomes M tensor_A B.
   Only the ordinary etale clauses are used, not the pro-etale assertions.
5. The K-flat computation of lem-pur-derived-change-of-rings (06YT and 06YY), on
   the identity resolution of P, identifies the derived extension of Q(P) with the
   localization of the extended complex, in D(B_T). Apply the scalar functor to
   the representing isomorphism Q(P) to K to obtain the displayed representation.
6. Transport bounded constructibility along that isomorphism. Apply
   lem-kun-flat-bounded-tor-amplitude (08G1) over B to its bounded flat model,
   obtaining the same interval against every degree-zero B-module sheaf.
No step assumes flatness or finite projective dimension of B over A. -/
theorem exists_etaleScalarFlatModel
    (T : Scheme.{u}) [IsNoetherian T]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory.Bounded
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hK : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K.obj))
    (_hTor : DerivedCategory.hasTorAmplitudeIn A T a b K.obj) :
    (∃ P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) ∧
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
      Nonempty (_root_.DerivedCategory.Q.obj P ≅ K.obj)) ∧
    (∀ P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) →
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) →
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) →
      Nonempty (_root_.DerivedCategory.Q.obj P ≅ K.obj) →
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        (HomologicalComplex.quasiIso (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        P ∧
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        (HomologicalComplex.quasiIso (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ∧
      (∀ q : ℤ, exactFunctor _ _ (tensorRight
        ((((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P).X q))) ∧
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P).X q)) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero
        ((((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P).X q)) ∧
      Nonempty ((ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj ≅
        _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))) ∧
    (∃ L : _root_.DerivedCategory.Bounded
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)),
      Nonempty (L.obj ≅
        (ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj)) ∧
    (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) i).obj
        ((ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj))) ∧
    DerivedCategory.hasTorAmplitudeIn B T a b
      ((ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj) := by
  have hbounded : DerivedCategory.isBoundedConstructible A T K.obj := by
    refine ⟨_hK, ?_⟩
    obtain ⟨c, hc⟩ := K.property.1
    obtain ⟨d, hd⟩ := K.property.2
    exact ⟨min c d, d, min_le_right _ _, fun i hi ↦ hi.elim
      (fun h ↦ (_root_.DerivedCategory.isGE_iff K.obj c).1 hc i (lt_of_lt_of_le h
        (min_le_left _ _)))
      (fun h ↦ (_root_.DerivedCategory.isLE_iff K.obj d).1 hd i h)⟩
  obtain ⟨P, hf, hc, hz, he⟩ :=
    (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A T a b _hab K.obj
      hbounded).1 _hTor
  have hp : ∀ q, exactFunctor _ _ (tensorRight (P.X q)) := by
    intro q
    exact (hf q).tensorRight
  have models : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) →
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) →
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) →
      Nonempty (_root_.DerivedCategory.Q.obj P ≅ K.obj) →
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        (HomologicalComplex.quasiIso (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        P ∧
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        (HomologicalComplex.quasiIso (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ∧
      (∀ q : ℤ, exactFunctor _ _ (tensorRight
        ((((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P).X q))) ∧
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P).X q)) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero
        ((((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P).X q)) ∧
      Nonempty ((ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj ≅
        _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P)) := by
    intro P hp hc hz he
    have hflat (q : ℤ) : ObjectProperty.flat (P.X q) := by
      refine ⟨?_, hp q⟩
      exact (exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight (P.X q)).symm (hp q)
    have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
      fun q hq ↦ hz q (.inl hq)
    have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
      fun q hq ↦ hz q (.inr hq)
    have hk := CochainComplex.kFlat_of_bounded_of_flat P a b hflat
    let E := ProEtale.etaleSheafExtendScalars φ T
    let Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
      (E.mapHomologicalComplex (.up ℤ)).obj P
    let : E.PreservesKFlatQuasiIso :=
      ProEtale.scalarExtension_preservesKFlat T.smallEtaleTopology φ
    have hQflat (q : ℤ) : ObjectProperty.flat (Q.X q) :=
      ProEtale.flat_etaleSheafExtendScalars_obj (φ := φ) (hflat q)
    have hQzero (q : ℤ) (hq : q < a ∨ b < q) : IsZero (Q.X q) :=
      E.map_isZero (hz q hq)
    have : Q.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
      fun q hq ↦ hQzero q (.inl hq)
    have : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
      fun q hq ↦ hQzero q (.inr hq)
    have hQk := CochainComplex.kFlat_of_bounded_of_flat Q a b hQflat
    have hcons := constructibleCoefficientSiteSquare T A B φ a b _hab P hz hc
    let adj : E.leftDerivedFunctor ⊣ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
      ProEtale.scalarDerivedAdjunction T.smallEtaleTopology φ
    let eF : ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ ≅
        E.leftDerivedFunctor :=
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).leftAdjointUniq adj
    have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hk
    obtain ⟨e⟩ := he
    let eQ : (ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj ≅
        _root_.DerivedCategory.Q.obj Q :=
      eF.app K.obj ≪≫ E.leftDerivedFunctor.mapIso
        (e.symm ≪≫ ((_root_.DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
      asIso (E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      _root_.DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).app Q
    exact ⟨hk, hQk, fun q ↦ (hQflat q).tensorRight, hcons.1, hQzero, ⟨eQ⟩⟩
  obtain ⟨-, -, hQf, -, hQz, ⟨eQ⟩⟩ := models P hp hc hz he
  let Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
    ((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P
  have hflat (q : ℤ) : ObjectProperty.flat (Q.X q) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (Q.X q)).symm (hQf q), hQf q⟩
  have : Q.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
    fun q hq ↦ hQz q (.inl hq)
  have : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    fun q hq ↦ hQz q (.inr hq)
  have ht := _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat Q a b hflat
  have hh := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht
  let L : _root_.DerivedCategory.Bounded
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    ⟨_root_.DerivedCategory.Q.obj Q, ⟨⟨a, hh.1⟩, ⟨b, hh.2⟩⟩⟩
  refine ⟨⟨P, hp, hc, hz, he⟩, models, ⟨L, ⟨eQ.symm⟩⟩, ?_, ?_⟩
  · intro i
    have hcons := (constructibleCoefficientSiteSquare T A B φ a b _hab P hz hc).2.2.2.1.1 i
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ i).obj (_root_.DerivedCategory.Q.obj Q)) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hcons
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ i).mapIso eQ).symm)
  · exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eQ.symm ht)

end AlgebraicGeometry.Etale
