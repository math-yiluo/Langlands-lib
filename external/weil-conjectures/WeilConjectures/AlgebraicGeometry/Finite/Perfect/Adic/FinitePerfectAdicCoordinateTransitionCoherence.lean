/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSourceNormalizationUniversal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Coherence of finite perfect adic coordinate transitions

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This descends a coherent pro-etale quotient system to specified etale origins.
The former assertion for arbitrary independent arrows and realizations was false;
its zero-arrow diagnostic is retained below. The parent existential statement
`finitePerfectAdic_descend_coordinate_transitions` is unchanged.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem comparison_coefficients_eq (Z : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    localIsomorphismComparisonCoefficients (X := Z) q =
      (ProEtale.pbcDerivedComparisonRestrict Z q).symm := by
  have he : normalizationPullbackIso Z.smallEtaleTopology (toProEt Z)
      (ProEt.topology Z) q = (ProEtale.pbcComparisonRestrict Z q).symm := by
    apply Iso.ext
    change normalizationPullbackMate Z.smallEtaleTopology (toProEt Z)
      (ProEt.topology Z) q = (ProEtale.pbcComparisonRestrict Z q).inv
    have hm := ProEtale.comparison_restrict_mate Z q
    have hs := congrArg
      (fun z ↦ ((mateEquiv (ProEtale.comparisonAdjunction (ModuleCat.{t + 1} S) Z)
        (ProEtale.comparisonAdjunction (ModuleCat.{t + 1} R) Z)).symm z))
      (congrArg (fun z ↦ TwoSquare.mk _ _ _ _ z) hm)
    simpa only [Equiv.symm_apply_apply, normalizationPullbackMate,
      ProEtale.comparisonAdjunction, ProEtale.comparisonLowerStar,
      ProEtale.comparisonUpperStar, Sheaf.restrictScalars,
      TwoSquare.mk] using hs.symm
  apply Iso.ext
  simp only [localIsomorphismComparisonCoefficients, he,
    ProEtale.pbcDerivedComparisonRestrict, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    Sheaf.restrictScalars, Category.assoc]

private theorem comparison_unit_square
    (Z : Scheme.{t}) {R S : Type (t + 1)} [CommRing R] [CommRing S]
    (q : R →+* S)
    (C : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{t + 1} R))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} R) Z).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars Z.smallEtaleTopology q)).unit.app C) ≫
      (localIsomorphismComparisonCoefficients q).hom.app
        ((ProEtale.pbcFixedScalarExtension Z.smallEtaleTopology q).obj C) =
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (ProEt.topology Z) q)).unit.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{t + 1} R) Z).mapDerivedCategory.obj C) ≫
      (normalizationRestrict (ProEt.topology Z) q).map
        ((ProEtale.pbcComparisonReduction Z q).hom.app C) := by
  rw [comparison_coefficients_eq Z q]
  exact unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology q))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology Z) q))
    (TwoSquare.mk _ _ _ _ (ProEtale.pbcDerivedComparisonRestrict Z q).inv) C

private theorem realization_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : D ⥤ C) (F : C ⥤ E) (G : D ⥤ E) (γ : R ⋙ F ≅ G)
    {X X' : C} {Y Y' : D}
    (d : X ⟶ R.obj Y) (d' : X' ⟶ R.obj Y')
    (a : X ≅ X') (b : Y ≅ Y')
    (h : d ≫ R.map b.hom = a.hom ≫ d') :
    F.map d ≫ γ.hom.app Y ≫ G.map b.hom =
      F.map a.hom ≫ F.map d' ≫ γ.hom.app Y' := by
  have hn := γ.hom.naturality b.hom
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Functor.map_comp_assoc, h, Functor.map_comp]
  simp only [Category.assoc]

-- Elaborating the two mate squares expands several derived-functor adjunctions.
/-- Coherent quotient-coordinate arrows descend through the supplied bounded-below
etale origins, preserving scalar realization and sourcewise universality.

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-coherence).

Proof: transpose each pro-etale quotient arrow through scalar extension. Its adjunct
is an isomorphism by the supplied normalization. Conjugate this isomorphism by the
specified origins and the canonical comparison/scalar-extension mate. Full faithfulness
with bounded-below target gives a unique etale isomorphism. Transpose it back to get
the etale coefficient arrow. The mate unit identity gives its exact comparison square.
The etale arrow is universal, and remains so after etale pullback. Compose each supplied
quotient realization with the inverse image of the specified origin comparison. The
comparison square and naturality of both scalar compositors give the required tower
square. This does not assert coherence for independently chosen arrows or isomorphisms. -/
theorem finitePerfectAdic_coordinate_transition_coherence
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (hKplus : ∀ n : ℕ, DerivedCategory.TStructure.t.plus (K n))
    (e : ∀ n : ℕ, ((ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj (K n) ≅ finitePerfectAdicQuotientCoordinates X d φ M V n)
    (dJ : ∀ n : ℕ, finitePerfectAdicQuotientCoordinates X d φ M V (n + 1) ⟶
      (normalizationRestrict (ProEt.topology V.left)
        (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj
          (finitePerfectAdicQuotientCoordinates X d φ M V n))
    (hJ : ∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (dJ n))))
    (actualJ : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.obj
            (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≅
      (finitePerfectAdicRestrictedTower X d W
        ((completedAdicReduction X d).obj M)).obj (op n))
    (hactualJ : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))))
            U.hom).mapDerivedCategory.map
            (dJ n) ≫
          (localIsomorphismProEtaleCoefficients U.hom
            (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
              (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≫
        (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
          ((ProEtale.upperStar
            (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
              U.hom).mapDerivedCategory.obj
                (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≫
          (actualJ U W f n).hom =
        (actualJ U W f (n + 1)).hom ≫
          (finitePerfectAdicRestrictedTower X d W
            ((completedAdicReduction X d).obj M)).map
              (homOfLE (Nat.le_succ n)).op) :
    ∃ dK : ∀ n : ℕ, K (n + 1) ⟶
        (normalizationRestrict V.left.smallEtaleTopology
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
    ∃ actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f n).obj
          ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
            (K n)) ≅
        (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
          (op n),
      (∀ (n : ℕ) (U : V.left.Etale), Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
            (dK n) U)))) ∧
      (∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
          (localProEtaleNormalization U.hom
            (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)) ≫
          (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
            ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
              (K n)) ≫
          (actual U W f n).hom =
        (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
            (homOfLE (Nat.le_succ n)).op) := by
  classical
  have hstep (n : ℕ) : ∃ δ : K (n + 1) ⟶
      (normalizationRestrict V.left.smallEtaleTopology
        (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
      (∀ U : V.left.Etale, Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) δ U)))) ∧
      (ProEtale.comparisonUpperStar
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))))
          V.left).mapDerivedCategory.map δ ≫
        (localIsomorphismComparisonCoefficients
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
            (K n) ≫
        (normalizationRestrict (ProEt.topology V.left)
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).map
            (e n).hom =
      (e (n + 1)).hom ≫ dJ n := by
    let R := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))
    let S := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
    let q : R →+* S := RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    let T := ProEtale.pbcFixedScalarExtension V.left.smallEtaleTopology q
    let P := ProEtale.pbcFixedScalarExtension (ProEt.topology V.left) q
    let aT := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars V.left.smallEtaleTopology q)
    let aP := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology V.left) q)
    let F := (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} R) V.left).mapDerivedCategory
    let G := (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} S) V.left).mapDerivedCategory
    let N := normalizationRestrict (ProEt.topology V.left) q
    let c := ProEtale.pbcComparisonReduction V.left q
    let bHom := (aP.homEquiv _ _).symm (dJ n)
    have hbHom : aP.unit.app _ ≫ N.map bHom = dJ n :=
      (aP.homEquiv _ _).apply_symm_apply (dJ n)
    let v : (StructuredArrow.mk (aP.unit.app
        (finitePerfectAdicQuotientCoordinates X d φ M V (n + 1))) : StructuredArrow _ N) ⟶
        StructuredArrow.mk (dJ n) :=
      StructuredArrow.homMk bHom hbHom
    have : IsIso v := isIso_of_isInitial (mkInitialOfLeftAdjoint _ aP _) (hJ n).some v
    have : IsIso bHom :=
      inferInstanceAs (IsIso ((StructuredArrow.proj _ _).map v))
    let b := asIso bHom
    let k : G.obj (T.obj (K (n + 1))) ≅ G.obj (K n) :=
      (c.app (K (n + 1))).symm ≪≫ P.mapIso (e (n + 1)) ≪≫ b ≪≫ (e n).symm
    obtain ⟨g, hg⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        (T.obj (K (n + 1))) (K n) (hKplus n)).2 k.hom
    have hg' : G.map g = k.hom := hg
    have : IsIso (G.map g) := by rw [hg']; infer_instance
    have : IsIso g := by
      rw [DerivedCategory.isIso_iff]
      intro i
      have : IsIso ((ProEtale.comparisonUpperStar (ModuleCat.{t + 1} S) V.left).map
          ((DerivedCategory.homologyFunctor _ i).map g)) :=
        (NatIso.isIso_map_iff
          ((ProEtale.comparisonUpperStar (ModuleCat.{t + 1} S)
            V.left).mapDerivedCategoryHomologyFunctorIso i) g).2
              (by dsimp only [Functor.comp_map]; infer_instance)
      exact isIso_of_reflects_iso _
        (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} S) V.left)
    let δ := aT.unit.app (K (n + 1)) ≫
      (normalizationRestrict V.left.smallEtaleTopology q).map g
    have hu : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk δ)) := by
      refine ⟨(mkInitialOfLeftAdjoint _ aT (K (n + 1))).ofIso
        (StructuredArrow.isoMk (asIso g) ?_)⟩
      rfl
    refine ⟨δ, (fun U ↦ etaleSourceNormalization_universal V.left q δ hu U), ?_⟩
    have hk : c.hom.app (K (n + 1)) ≫ G.map g ≫ (e n).hom =
        P.map (e (n + 1)).hom ≫ b.hom := by
      rw [hg']
      simp only [k, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        Iso.app_inv, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id, Category.comp_id]
    have hβ := (localIsomorphismComparisonCoefficients (X := V.left) q).hom.naturality g
    dsimp only [Functor.comp_map] at hβ
    change F.map δ ≫
        (localIsomorphismComparisonCoefficients q).hom.app (K n) ≫ N.map (e n).hom =
      (e (n + 1)).hom ≫ dJ n
    dsimp only [δ]
    rw [Functor.map_comp, Category.assoc, reassoc_of% hβ]
    rw [← Category.assoc, comparison_unit_square V.left q (K (n + 1))]
    simp only [Category.assoc]
    rw [← N.map_comp, ← N.map_comp, hk, N.map_comp]
    have hn := aP.unit.naturality (e (n + 1)).hom
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    change (e (n + 1)).hom ≫ aP.unit.app _ =
      aP.unit.app _ ≫ N.map (P.map (e (n + 1)).hom) at hn
    rw [← Category.assoc, ← hn, Category.assoc]
    have hb : aP.unit.app _ ≫ N.map b.hom = dJ n :=
      (aP.homEquiv _ _).apply_symm_apply (dJ n)
    exact congrArg (fun z ↦ (e (n + 1)).hom ≫ z) hb
  choose dK huniversal hcomp using hstep
  let actual (U : V.left.ProEt) (W : X.ProEt)
      (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :=
    (finitePerfectAdicScalarRealization X d V U W f n).mapIso
      ((ProEtale.upperStar
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.mapIso
          (e n)) ≪≫ actualJ U W f n
  refine ⟨dK, actual, huniversal, ?_⟩
  intro U W f n
  let R := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))
  let S := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let q : R →+* S := RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let F := (ProEtale.upperStar (ModuleCat.{t + 1} R) U.hom).mapDerivedCategory
  let G := (ProEtale.upperStar (ModuleCat.{t + 1} S) U.hom).mapDerivedCategory
  let E := normalizationRestrict (ProEt.topology V.left) q
  let N := normalizationRestrict (ProEt.topology U.left) q
  let dC := (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} R) V.left).mapDerivedCategory.map
    (dK n) ≫
    (localIsomorphismComparisonCoefficients q).hom.app (K n)
  let dU := F.map (dJ n) ≫
    (localIsomorphismProEtaleCoefficients U.hom q).hom.app
      (finitePerfectAdicQuotientCoordinates X d φ M V n)
  have hl := realization_square E F (G ⋙ N)
    (localIsomorphismProEtaleCoefficients U.hom q)
    dC (dJ n) (e (n + 1)) (e n) (by
      simpa only [dC, Category.assoc] using hcomp n)
  have hl' : localProEtaleNormalization U.hom q (dK n) ≫
      N.map (G.map (e n).hom) = F.map (e (n + 1)).hom ≫ dU := by
    simpa only [dC, dU, localProEtaleNormalization, localProEtaleComparisonCoefficients,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Functor.comp_map, Functor.map_comp,
      Category.assoc, localProEtaleComparison, Functor.fromPUnit, Functor.const,
      Functor.comp_obj, F, G] using hl
  have hr := realization_square N
    (finitePerfectAdicScalarRealization X d V U W f (n + 1))
    (finitePerfectAdicScalarRealization X d V U W f n)
    (finitePerfectAdicScalarCoherence X d V U W f n)
    (localProEtaleNormalization U.hom q (dK n)) dU
    (F.mapIso (e (n + 1))) (G.mapIso (e n)) hl'
  have heq := congrArg (fun k ↦ k ≫ (actualJ U W f n).hom) hr
  simp only [Category.assoc] at heq
  rw [hactualJ U W f n] at heq
  simpa only [actual, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using heq

end AlgebraicGeometry.Scheme
