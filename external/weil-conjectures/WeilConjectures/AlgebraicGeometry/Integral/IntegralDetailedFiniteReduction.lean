/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement

/-! # Finite reduction comparison for integral coefficient presentations

## References

* Bhatt--Scholze, Section 6.5, convention before Definition 6.5.1
* Bhatt--Scholze, Lemma 4.2.12 and Lemma 6.8.2(1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open ProEtale Opposite
open WeilConjectures

private theorem fixed_finite_restrict {X : Scheme.{u}}
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (r : A →+* B)
    (hr : Function.Surjective r)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (h : ProEtale.IsFiniteLocallyConstant B F) :
    ProEtale.IsFiniteLocallyConstant A ((Sheaf.restrictScalars _ r).obj F) := by
  have : (ModuleCat.restrictScalars.{u + 1} r).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} r).isLeftAdjoint
  obtain ⟨I, W, g, hg, h⟩ := h
  refine ⟨I, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := h i
  have hM' : Module.Finite A ((ModuleCat.restrictScalars.{u + 1} r).obj M) := by
    obtain ⟨s, hs⟩ := hM.fg_top
    refine ⟨⟨s, Submodule.eq_top_iff'.2 fun x ↦ ?_⟩⟩
    have hx : x ∈ Submodule.span B (s : Set M) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul b y _ hy =>
      obtain ⟨a, rfl⟩ := hr b
      exact Submodule.smul_mem _ a hy
  exact ⟨(ModuleCat.restrictScalars.{u + 1} r).obj M, hM',
    ⟨(ProEtale.upperStarRestrictScalarsIso.{u} r (g i)).app F ≪≫
      (sheafCompose (ProEt.topology (W i))
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r)).mapIso e ≪≫
        (constantCommuteCompose (ProEt.topology (W i))
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r)).app M⟩⟩

private theorem fixed_constructible_restrict {X : Scheme.{u}}
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (r : A →+* B)
    (hr : Function.Surjective r)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (h : ProEtale.IsConstructible B F) :
    ProEtale.IsConstructible A ((Sheaf.restrictScalars _ r).obj F) := by
  obtain ⟨S, h⟩ := h
  refine ⟨S, fun i ↦ ?_⟩
  exact ProEtale.isFiniteLocallyConstant_of_iso
    ((ProEtale.upperStarRestrictScalarsIso r (S.immersion i)).app F).symm
    (fixed_finite_restrict A B r hr _ (h i))

private theorem fixed_constructible_restrict_iff {X : Scheme.{u}}
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (r : A ≃+* B)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)) :
    ProEtale.IsConstructible A ((Sheaf.restrictScalars _ r.toRingHom).obj F) ↔
      ProEtale.IsConstructible B F := by
  constructor
  · intro h
    have h' := fixed_constructible_restrict B A r.symm.toRingHom r.symm.surjective _ h
    let e : (Sheaf.restrictScalars _ r.toRingHom ⋙
        Sheaf.restrictScalars _ r.symm.toRingHom).obj F ≅ F :=
      (fullyFaithfulSheafToPresheaf (ProEt.topology X) _).preimageIso
        (Functor.isoWhiskerLeft F.obj
          ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv r).unitIso.symm))
    exact ProEtale.isConstructible_of_iso e h'
  · exact fixed_constructible_restrict A B r.toRingHom r.surjective F

private def constantRestrictionEncoding (T : Scheme.{u})
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (r : A →+* B) :
    pbcRestrict ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom r)) ⋙ CoefficientSerre.proEtaleModuleRestriction T A ≅
    CoefficientSerre.proEtaleModuleRestriction T B ⋙ Sheaf.restrictScalars _ r := by
  let c := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom r)
  have hc (U : T.ProEtᵒᵖ) (a : A) :
      (c.hom.app U).hom
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U a) =
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of B))).app U (r a) := by
    have h := congr_app (toSheafify_naturality (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom r))) U
    exact (ConcreteCategory.congr_hom h a).symm
  refine NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf (ProEt.topology T) _).preimageIso
      (NatIso.ofComponents (fun U ↦
        let P := ((pbcRestrict c ⋙ CoefficientSerre.proEtaleModuleRestriction T A).obj
          M).obj.obj U
        let Q := ((CoefficientSerre.proEtaleModuleRestriction T B ⋙
          Sheaf.restrictScalars _ r).obj M).obj.obj U
        LinearEquiv.toModuleIso (show P ≃ₗ[A] Q from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ ?_ }))
        (fun f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  change (c.hom.app U).hom
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U a) • (show M.val.obj U from x) =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of B))).app U (r a) • (show M.val.obj U from x)
  rw [hc]

private def detailedFiniteComparison (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) :
    integralDetailedTransport T l E ⋙ pbcConstantReduction T (pbcIntegralDatum l E) n ≅
      scalarReductionDerivedExtension.{u, u} l E T n ⋙
        pbcDerivedRestrict ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom) := by
  let d := pbcIntegralDatum l E
  let e := purCoefficientIso l E T
  let b := IntegralCoefficientPresentation.level l E T (integralCoefficientULift l E) n
  let π := pbcAdicProjection T d n
  let ρ := completedIntegralCommRingProjectionUnrestricted l E T n
  let κ := pbcLevelConstantComparison T d n
  let q := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
    (integralCoefficientULift l E n).toCommRingCatIso
  have heR : (adicLisseForget T).mapIso e =
      integralDetailedCoefficientComparison T l E :=
    (purCoefficientIso_existsUnique l E T).exists.choose_spec
  have he : π ≫ b.hom = e.hom ≫ ρ := by
    apply (adicLisseForget T).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    have hn := (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec n
    change (integralDetailedCoefficientComparison T l E).hom ≫ _ = _ at hn
    rw [← heR] at hn
    exact hn.symm
  have := (IntegralCoefficientPresentation.restrict_equivalence e).1
  have := (IntegralCoefficientPresentation.restrict_equivalence b).1
  have : (pbcDerivedRestrict e.hom).IsEquivalence := by
    change (pbcRestrict e.hom).mapDerivedCategory.IsEquivalence
    infer_instance
  have : (pbcDerivedRestrict b.hom).IsEquivalence := by
    change (pbcRestrict b.hom).mapDerivedCategory.IsEquivalence
    infer_instance
  let r := IntegralCoefficientPresentation.restrictionSquare π b.hom e.hom ρ he
  let α := (IntegralCoefficientPresentation.square_iso
    (pbcDerivedScalarAdjunction π) (pbcDerivedScalarAdjunction ρ)
    (pbcDerivedRestrict e.hom) (pbcDerivedRestrict b.hom)
    (IntegralCoefficientPresentation.derivedSquare e b π ρ r)).choose
  let β := Adjunction.leftAdjointUniq
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E T n).choose
    (pbcDerivedScalarAdjunction ρ)
  have hκ : κ.hom ≫ b.hom = q.hom := by
    simp [b, IntegralCoefficientPresentation.level, κ, q]
  have h : integralDetailedTransport T l E = pbcDerivedRestrict e.hom := by
    have := (integralDetailedCoefficientRestriction_exact T l E).1
    have := (integralDetailedCoefficientRestriction_exact T l E).2
    dsimp only [integralDetailedTransport, pbcDerivedRestrict, pbcRestrict]
    simp only [← congrArg Iso.hom heR]
    rfl
  rw [h]
  exact Functor.isoWhiskerRight α (pbcDerivedRestrict κ.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pbcDerivedRestrictComp κ.hom b.hom q.hom hκ) ≪≫
    Functor.isoWhiskerRight β.symm (pbcDerivedRestrict q.hom)

/-- At one finite level, the normalized coefficient transport preserves exactly
constructibility and any specified cohomological interval. -/
theorem integralDetailedFiniteReduction
    (T : Scheme.{u}) [IsNoetherian T] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (n : ℕ) (a b : ℤ) :
    (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) T
        ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T n).obj K) ∧
      proEtaleCohomologicalSupport
        ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T n).obj K) ⊆
          Set.Icc a b) ↔
    (((pbcConstantReduction T (pbcIntegralDatum l E) n).obj
        ((integralDetailedTransport T l E).obj K)).IsGE a ∧
      ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj
        ((integralDetailedTransport T l E).obj K)).IsLE b ∧
      DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf T
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj
          ((integralDetailedTransport T l E).obj K))) := by
  classical
  let A := PbcQuotient (pbcIntegralDatum l E) n
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let X := (scalarReductionDerivedExtension.{u, u} l E T n).obj K
  let Y := (pbcConstantReduction T (pbcIntegralDatum l E) n).obj
    ((integralDetailedTransport T l E).obj K)
  let e := integralCoefficientULift l E n
  let c := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
    e.toCommRingCatIso
  let R := pbcRestrict c.hom
  have : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : R.IsEquivalence :=
    (IntegralCoefficientPresentation.restrict_equivalence c).1
  let hH (q : ℤ) : (DerivedCategory.homologyFunctor _ q).obj Y ≅
      R.obj ((DerivedCategory.homologyFunctor _ q).obj X) :=
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((detailedFiniteComparison T l E n).app K) ≪≫
        ((R.mapDerivedCategoryHomologyFunctorIso q).app X).symm
  have hz (q : ℤ) : IsZero ((DerivedCategory.homologyFunctor _ q).obj Y) ↔
      IsZero ((DerivedCategory.homologyFunctor _ q).obj X) := by
    rw [(hH q).isZero_iff]
    constructor
    · intro h
      apply (IsZero.iff_id_eq_zero _).mpr
      apply R.map_injective
      exact h.eq_of_src _ _
    · exact R.map_isZero
  have hc (q : ℤ) : IsConstructibleProEtaleCoefficientModuleSheaf T A
      ((DerivedCategory.homologyFunctor _ q).obj Y) ↔
      IsConstructibleProEtaleModuleSheaf T B
        ((DerivedCategory.homologyFunctor _ q).obj X) := by
    rw [CoefficientSerre.coefficient_constructible_iff,
      proEtaleModuleRestriction_constructible_iff]
    let t := (CoefficientSerre.proEtaleModuleRestriction T A).mapIso (hH q) ≪≫
      (constantRestrictionEncoding T A (ULift.{u + 1} B) e.toRingHom).app
        ((DerivedCategory.homologyFunctor _ q).obj X)
    constructor
    · intro h
      apply (fixed_constructible_restrict_iff A (ULift.{u + 1} B) e _).mp
      exact ProEtale.isConstructible_of_iso t h
    · intro h
      apply ProEtale.isConstructible_of_iso t.symm
      exact (fixed_constructible_restrict_iff A (ULift.{u + 1} B) e _).mpr h
  constructor
  · rintro ⟨hconst, hs⟩
    refine ⟨(DerivedCategory.isGE_iff Y a).mpr ?_,
      (DerivedCategory.isLE_iff Y b).mpr ?_, fun q ↦ (hc q).mpr (hconst.2 q)⟩
    · intro q hq
      apply (hz q).mpr
      by_contra hne
      exact (not_le_of_gt hq) (hs hne).1
    · intro q hq
      apply (hz q).mpr
      by_contra hne
      exact (not_le_of_gt hq) (hs hne).2
  · rintro ⟨ha, hb, hconst⟩
    have hs : proEtaleCohomologicalSupport X ⊆ Set.Icc a b := by
      intro q hq
      constructor
      · by_contra hqa
        exact hq ((hz q).mp ((DerivedCategory.isGE_iff Y a).mp ha q (lt_of_not_ge hqa)))
      · by_contra hbq
        exact hq ((hz q).mp ((DerivedCategory.isLE_iff Y b).mp hb q (lt_of_not_ge hbq)))
    exact ⟨⟨(Set.finite_Icc a b).subset hs, fun q ↦ (hc q).mp (hconst q)⟩, hs⟩

end AlgebraicGeometry.Scheme
