/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ConstructibleFiniteHeart
import all WeilConjectures.AlgebraicGeometry.IntegralContinuousEncodingConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTriangulated
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
import all WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.IntegralReductionPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion

/-! # Upper bounds for integral constructible sheaves -/

@[expose] public section

set_option autoImplicit false

set_option synthInstance.maxSize 2048

universe u

-- Pin the site universe before synthesizing the generic tensor structures.
attribute [local instance 100000] WeilConjectures.instEssentiallySmallProEt_weilConjectures

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open FiniteDiscreteOrdinary

attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

-- Over a field every stalk is flat; bounded devissage gives finite Tor amplitude.
private theorem field_finiteTor (B : Type (u + 1)) [Field B] (Z : Scheme.{u})
    (K : Etale.DerivedCategoryModule B Z)
    (hK : DerivedCategory.TStructure.t.bounded K) :
    _root_.DerivedCategory.finiteTorAmplitude _ K := by
  let P := _root_.DerivedCategory.finiteTorAmplitude
    (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))
  have hs (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    exact ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      ((Etale.flat_iff_forall_flat_sheafFiber_obj M).2 fun _ ↦
        (ModuleCat.flat_iff_flat _).2 inferInstance)⟩
  apply DerivedCategory.prop_of_bounded_of_degreewise P
    (fun _ h ↦ P.prop_of_isZero h)
    (fun T hT h₁ h₃ ↦ P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃)
    (fun _ ↦ ⊤) ?_ K hK (fun _ ↦ trivial)
  intro q M _
  exact P.prop_of_iso (((DerivedCategory.singleFunctors _).shiftIso
    (-q) q 0 (by omega)).app M) (P.le_shift (-q) _ (hs M))

-- Bhatt--Scholze 5.4.3 and the classical finite-type direct-image theorem.
private theorem finite_field_image
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k ≠ ℓ)]
    (B : Type u) [Field B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B] (hB : (ℓ : B) = 0)
    (X Y : Over (Spec (.of k) : Scheme.{u}))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (K : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient B) X.left) :
    ∃ N : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient B) Y.left,
      Nonempty (N.obj ≅ ((CondensedRing.moduleObjectDerivedPushforward
        (FiniteDiscreteOrdinary.coefficient B) f.left).obj K.obj)) := by
  classical
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists B T).some
  obtain ⟨hreal, hpush⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization_of_field k B E
  obtain ⟨a, b, ht⟩ := K.property.2
  have hab : a ≤ max a b := le_max_left _ _
  have ht' := ht.mono le_rfl (le_max_right a b)
  obtain ⟨eX, ⟨heX⟩⟩ := hreal X a (max a b) hab
  let L := eX.inverse.obj ⟨K.obj, K.property.1, ht'⟩
  let eL : (FiniteDiscreteOrdinary.internalEtaleRealization B X.left (E X.left)).obj
      L.obj ≅ K.obj :=
    (heX.app L).symm ≪≫ (ObjectProperty.ι _).mapIso
      (eX.counitIso.app ⟨K.obj, K.property.1, ht'⟩)
  have hell : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k) (Fact.out : ℓ.Prime)
      (Fact.out : ringChar k ≠ ℓ))
  have : HasInvertibleExponent (ULift.{u + 1} B) (Spec (.of k)) := by
    refine ⟨ℓ, (Fact.out : ℓ.Prime).pos, ?_, ?_⟩
    · apply ULift.ext
      exact hB
    · simpa only [map_natCast] using hell.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hLc := (etaleBC_iff B X.left L.obj).mp L.property.1
  have hQ := Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType
    (ULift.{u + 1} B) f.left X.hom Y.hom (Over.w f) L.obj hLc
  let D := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f.left
  let Q := D.rightDerivedFunctor.obj L.obj
  obtain ⟨c, d, htQ⟩ := field_finiteTor (ULift.{u + 1} B) Y.left Q hQ.1
  let r := min c d
  let s := max c d
  have hrs : r ≤ s := min_le_max
  have htQ' : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} B) Y.left r s Q :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (htQ.mono (min_le_left c d) (le_max_right c d))
  obtain ⟨eY, ⟨heY⟩⟩ := hreal Y r s hrs
  let N := eY.functor.obj ⟨Q, (etaleBC_iff B Y.left Q).mpr hQ, htQ'⟩
  have hplus : DerivedCategory.TStructure.t.plus L.obj := hLc.1.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiCompact f.left := inferInstance
  have : QuasiSeparated f.left := inferInstance
  obtain ⟨epush⟩ := hpush X Y f
  let eN := (heY.app ⟨Q, (etaleBC_iff B Y.left Q).mpr hQ, htQ'⟩) ≪≫
    epush.app ⟨L.obj, hplus⟩ ≪≫
      (CondensedRing.moduleObjectDerivedPushforward
        (FiniteDiscreteOrdinary.coefficient B) f.left).mapIso eL
  exact ⟨⟨N.obj, N.property.1, r, s, N.property.2⟩, ⟨eN⟩⟩

-- Serre, Local Fields I.1: ell belongs to the maximal ideal of the integer ring.
private theorem residue_killed (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (l : Padic.coefficientExtensionRing l E 1) = 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (l : Padic.coefficientExtensionIntegers l E) ∈
    Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
  rw [pow_one, hgen]
  apply (h.2.1 _).2
  have he := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
  change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
  rw [show (l : E) = algebraMap (Padic l) E (l : Padic l) by simp]
  change spectralNorm (Padic l) E (algebraMap (Padic l) E (l : Padic l)) < 1
  rw [he]
  exact Padic.norm_p_lt_one

-- The maximal ideal is the open ball of radius one, hence its quotient is discrete.
private theorem residue_discrete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E 1) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let I := Padic.coefficientExtensionIdeal l E 1
  apply QuotientAddGroup.discreteTopology (N := I.toAddSubgroup)
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hi : I = Padic.coefficientExtensionMaximalIdeal l E := by
    change Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1 = _
    rw [pow_one, hgen]
  have hs : (I.toAddSubgroup : Set (Padic.coefficientExtensionIntegers l E)) =
      {x : Padic.coefficientExtensionIntegers l E | ‖(x : E)‖ < 1} := by
    ext x
    change x ∈ I ↔ ‖(x : E)‖ < 1
    rw [hi]
    exact h.2.1 x
  rw [hs]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

-- Bhatt--Scholze 6.5.9 and 6.8.11: completeness and residue detect the integral image.
private theorem integral_image
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k) : Scheme.{u}))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (K : DerivedCategory (AdicCompletion.Modules ℓ E X.left))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E) X.left K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E) Y.left
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.integerRing ℓ E) f.left).obj K) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsNoetherian X.left := ⟨⟩
  let : IsNoetherian Y.left := ⟨⟩
  obtain ⟨hχ, hpush⟩ := internal_integral_direct_image_limits ℓ E f.left
  change IsIso (integralReductionPullbackMap ℓ E f.left 0) at hχ
  let := hχ
  let adj := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.integerRing ℓ E) f.left).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.integerRing ℓ E) f.left)
  let adj' := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.quotientRing ℓ E 1) f.left).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.quotientRing ℓ E 1) f.left)
  obtain ⟨hcomplete, hmate⟩ := hpush K
  obtain ⟨hinput, _⟩ := internal_integral_residue_criterion ℓ E X.left
  obtain ⟨houtput, _⟩ := internal_integral_residue_criterion ℓ E Y.left
  obtain ⟨hcK, hrK, htK⟩ := (hinput K).mp hK
  let c := adj'.homEquiv _ _
    (inv ((integralReductionPullbackMap ℓ E f.left 0).app
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.integerRing ℓ E) f.left).obj K)) ≫
      (AdicCompletion.derivedReduction ℓ E X.left 0).map (adj.counit.app K))
  have : IsIso c := hmate
  have h := (Padic.coefficientExtensionIntegers_dvr ℓ E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer ℓ E} =
      Padic.coefficientExtensionMaximalIdeal ℓ E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal ℓ E).IsMaximal := h.2.2.2.2.1
  have hm : (Padic.coefficientExtensionIdeal ℓ E 1).IsMaximal := by
    change (Ideal.span {Padic.coefficientExtensionUniformizer ℓ E} ^ 1).IsMaximal
    rw [pow_one, hgen]
    exact hmax
  let : Field (Padic.coefficientExtensionRing ℓ E 1) := @Ideal.Quotient.field _ _ _ hm
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let : Finite (Padic.coefficientExtensionRing ℓ E 1) :=
    Padic.finite_coefficientExtensionRing ℓ E 1 le_rfl
  let := residue_discrete ℓ E
  obtain ⟨N, ⟨hfinite⟩⟩ := finite_field_image ℓ k (Padic.coefficientExtensionRing ℓ E 1)
    (residue_killed ℓ E) X Y f
    ⟨((AdicCompletion.derivedReduction ℓ E X.left 0).obj K), hrK, htK⟩
  let e := asIso c
  let := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.quotientRing ℓ E 1) Y.left).2.1
  exact (houtput _).mpr ⟨hcomplete hcK,
    (constantModelBoundedConstructible (DerivedNakayama.quotientRing ℓ E 1) Y.left).prop_of_iso
       (hfinite ≪≫ e.symm) N.property.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso (hfinite ≪≫ e.symm) N.property.2⟩

private lemma constant_model_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply constantModelConstructible_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

private instance coefficient_lift_finite (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] :
    FiniteDimensional (Padic ℓ) (ULift.{u} F) :=
  (ULift.moduleEquiv (R := Padic ℓ) (M := F)).symm.finiteDimensional

private theorem coefficient_lift_absoluteValue (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] (x : ULift.{u} F) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} F) x =
      Padic.coefficientExtensionAbsoluteValue ℓ F x.down := by
  let a := Padic.coefficientExtensionAbsoluteValue ℓ F
  let b : AbsoluteValue (ULift.{u} F) ℝ :=
    { toFun := fun y ↦ a y.down
      map_mul' := fun y z ↦ a.map_mul y.down z.down
      nonneg' := fun y ↦ a.nonneg y.down
      eq_zero' := fun y ↦ by
        constructor
        · intro hy
          apply ULift.ext
          exact a.eq_zero.mp hy
        · rintro rfl
          exact map_zero a
      add_le' := fun y z ↦ a.add_le y.down z.down }
  have hb : ∀ y : Padic ℓ, b (algebraMap (Padic ℓ) (ULift.{u} F) y) = ‖y‖ := by
    intro y
    exact spectralNorm_extends (K := Padic ℓ) (L := F) y
  exact (spectralNorm_unique_field_norm_ext hb x).symm

private theorem coefficient_lift_memIntegers (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] (x : ULift.{u} F) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} F) ↔
      x.down ∈ Padic.coefficientExtensionIntegers ℓ F := by
  rw [Padic.mem_coefficientExtensionIntegers, Padic.mem_coefficientExtensionIntegers,
    coefficient_lift_absoluteValue]

attribute [local irreducible] Padic.coefficientExtensionIntegers

private def coefficient_lift_integers (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] :
    Padic.coefficientExtensionIntegers ℓ F ≃+*
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} F) where
  toFun x := ⟨ULift.up x.val, (coefficient_lift_memIntegers ℓ F _).2 x.property⟩
  invFun x := ⟨x.val.down, (coefficient_lift_memIntegers ℓ F _).1 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- The identity on small coefficients followed by ULift is an isometry of integer rings.
private theorem normed_point_iso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [hE : NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    Nonempty (Mon.mk (CondensedRing.integralCoeff.{u} ℓ E) ≅
      Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} E))) := by
  let R := CondensedRing.continuousIntegers ℓ E
  let S := Padic.coefficientExtensionIntegers ℓ (ULift.{u} E)
  let e₀ : R ≃+* Padic.coefficientExtensionIntegers ℓ E :=
    { toFun := fun x ↦ ⟨x.val, by
        rw [← CondensedRing.continuousIntegers_eq ℓ E]; exact x.property⟩
      invFun := fun x ↦ ⟨x.val, by
        change x.val ∈ CondensedRing.continuousIntegers ℓ E
        rw [CondensedRing.continuousIntegers_eq ℓ E]; exact x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let e : R ≃+* S := e₀.trans (coefficient_lift_integers.{u} ℓ E)
  let nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E)).toNormedField
  let : TopologicalSpace (ULift.{u} E) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let sm : MetricSpace R := @Subtype.metricSpace E _ hE.toMetricSpace
  let tm : MetricSpace S := @Subtype.metricSpace (ULift.{u} E) _ nf.toMetricSpace
  let : PseudoEMetricSpace R := sm.toPseudoMetricSpace.toPseudoEMetricSpace
  let : PseudoEMetricSpace S := tm.toPseudoMetricSpace.toPseudoEMetricSpace
  have he : Isometry e := by
    apply @Isometry.of_dist_eq _ _ sm.toPseudoMetricSpace tm.toPseudoMetricSpace
    intro x y
    change spectralNorm ℚ_[ℓ] (ULift.{u} E) (ULift.up (-x.val + y.val)) =
      @dist E hE.toMetricSpace.toDist x.val y.val
    rw [hE.dist_eq]
    exact (coefficient_lift_absoluteValue ℓ E _).trans
      (NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (-x.val + y.val)).symm
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheaf.{u} R ≅
      DerivedNakayama.integerRingSheaf ℓ (ULift.{u} E) :=
    { hom := ⟨{
        app := fun T ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous T.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun T ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous T.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext T x; apply ULift.ext; ext t; rfl
      inv_hom_id := by ext T x; apply ULift.ext; ext t; rfl }
  let G := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (G.mapIso c).hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  exact ⟨Mon.mkIso' (G.mapIso c)⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include ℓ k

/-- Integral single-sheaf case of finite-type finiteness.

Source: Bhatt--Scholze, Lemmas 6.5.9 and 6.7.2, Proposition 6.8.11(3).
(auxiliary; not a blueprint node)

Proof: identify the given closed unit ball with the spectral integer ring after
universe lifting. The ring equivalence is an isometry by uniqueness of the extended
absolute value, so postcomposition induces an isomorphism of condensed rings.
Restriction along it preserves constructibility and identifies the degree-zero
complexes. The internal constant-model comparison and the integral residue criterion
make this complex complete with bounded constructible residue of finite Tor amplitude.
Direct image preserves completeness, and its canonical residue mate is invertible.
The finite internal-etale realization identifies the residue direct image with the
classical finite-type etale direct image, which is bounded constructible. Over the
residue field every module is flat, so bounded devissage also gives finite Tor
amplitude. The converse integral residue criterion gives a bounded integral image.
Take its upper endpoint and reflect the cohomological vanishing through the exact
coefficient equivalence. Zero sheaves and empty schemes are included. -/
theorem finiteTypeIntegralHeart_boundedAbove
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  obtain ⟨e⟩ := normed_point_iso.{u} ℓ E
  let T (Z : Scheme.{u}) :
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Z) ⥤
      AdicCompletion.Modules ℓ (ULift.{u} E) Z :=
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap e.inv.hom Z)
  have (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  have hG := integral_internal_constant_models ℓ (ULift.{u} E) X.left
    ((T X.left).obj F) (_root_.constructible_comap (coefficientMap e.inv.hom X.left) hF)
  let K := (DerivedCategory.singleFunctor _ 0).obj F
  have hK : constantModelBoundedConstructible
      (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.left
      ((T X.left).mapDerivedCategory.obj K) := by
    let := (constantModelConstructibleFiniteTor_wellDefined
      (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.left).2.1
    exact (constantModelBoundedConstructible _ _).prop_of_iso
      (((T X.left).mapDerivedCategorySingleFunctor 0).app F).symm
      (constant_model_single _ _ _ hG)
  obtain ⟨b, hb⟩ := (integral_image ℓ (ULift.{u} E) k X Y f _ hK).1.2
  refine ⟨b, ?_⟩
  have hi := (CondensedRing.derivedComapLowerStarIso e.inv.hom f.left).app K
  have hb' := (DerivedCategory.isLE_iff _ b).mp hb
  rw [DerivedCategory.isLE_iff]
  intro q hq
  apply (T Y.left).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  exact (hb' q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso hi)

end AlgebraicGeometry.ProEtale.CondensedRing
