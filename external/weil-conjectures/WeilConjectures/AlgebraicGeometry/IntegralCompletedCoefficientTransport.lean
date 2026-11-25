/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-! # Canonical completed integral coefficient transport

The projection-normalized coefficient constructions are independent of the
stratified-perfect theorem and its geometric hypotheses.
Source: Bhatt--Scholze, Section 6.5
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The quotient coefficient identification induced by the canonical valuation-ring lift.
The normalization on representatives determines the equivalence uniquely. The source
uses the recorded valuation ring lifted to the small site's coefficient universe.
Source: blueprint coefficient conventions, order 411; Bhatt--Scholze, Section 6.5
(auxiliary; not a blueprint node).
Proof: ULift.down is a ring equivalence from the recorded lifted valuation ring to the
original valuation ring. It sends the recorded lifted uniformizer to the original
uniformizer, and hence identifies their principal ideals and every positive power.
Descend this equivalence to the quotients and lift its target. Surjectivity of the
quotient map proves uniqueness from the displayed representative formula. -/
theorem integralCoefficientULift_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ∃! e : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ x : PbcIntegralRing l E,
        e (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down) := by
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E :=
    ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E (n + 1) =
      Ideal.map e.toRingHom ((pbcIntegralDatum l E).ideal ^ (n + 1)) := by
    simp [pbcIntegralDatum, Padic.coefficientExtensionIdeal, Ideal.map_pow,
      Ideal.map_span, Set.image_singleton, e, pbcUniformizer]
    rfl
  let q := Ideal.quotientEquiv _ _ e hI
  refine ⟨q.trans ULift.ringEquiv.symm, ?_, ?_⟩
  · intro x
    change ULift.up (q (Ideal.Quotient.mk _ x)) = _
    rw [Ideal.quotientEquiv_mk]
    rfl
  · intro e' he'
    apply RingEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (he' x).trans (by
      change ULift.up (Ideal.Quotient.mk _ x.down) =
        ULift.up (q (Ideal.Quotient.mk _ x))
      rw [Ideal.quotientEquiv_mk]
      rfl)

/-- The uniquely normalized quotient equivalence, not an arbitrary field identification.
Source: blueprint coefficient conventions, order 411; Bhatt--Scholze, Section 6.5
(auxiliary; not a blueprint node). -/
def integralCoefficientULift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  (integralCoefficientULift_exists l E n).exists.choose

/-- The finite-level coefficient isomorphism: undo the normalized functions-sheaf
presentation, apply the quotient lift and forget commutativity.
Source: Bhatt--Scholze, Definition 6.5.1
(auxiliary; not a blueprint node). -/
def integralDetailedLevelComparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (adicLisseForget T).obj
        ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)) ≅
      WeilConjectures.integralCoefficientSheaf l E T n :=
  (adicLisseForget T).mapIso
    ((pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
        (integralCoefficientULift l E n).toCommRingCatIso)

/-- The unique completed coefficient comparison compatible with every finite projection.
This keeps the detailed definition's actual ring and positive reduction functors.
Source: Bhatt--Scholze, Definition 6.5.1
(auxiliary; not a blueprint node).
Proof: the normalized finite-level comparisons commute with transitions, as can be
checked on residue representatives. Apply the limit universal property. Forgetting
commutativity preserves limits, so both rings are limits of the same quotient system.
The projection identities determine a unique isomorphism. -/
theorem integralDetailedCoefficientComparison_exists
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃! e : (adicLisseForget T).obj
        (pbcAdicCompletion T (pbcIntegralDatum l E)) ≅
          WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T,
      ∀ n : ℕ,
        e.hom ≫ limit.π (WeilConjectures.integralCoefficientSheafSystem l E T) (op n) =
          (adicLisseForget T).map
              (pbcAdicProjection T (pbcIntegralDatum l E) n) ≫
            (integralDetailedLevelComparison T l E n).hom := by
  let d := pbcIntegralDatum l E
  let F := adicLisseForget T
  let C := constantSheaf (ProEt.topology T) CommRingCat.{u + 1}
  have hq (n : ℕ) (x : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ x) =
        ULift.up (Ideal.Quotient.mk _ x.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec x
  have htrans (n : ℕ) :
      CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ≫
        (integralCoefficientULift l E n).toCommRingCatIso.hom =
      (integralCoefficientULift l E (n + 1)).toCommRingCatIso.hom ≫
        CommRingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom).comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              ULift.ringEquiv.toRingHom)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change integralCoefficientULift l E n
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1) (Ideal.Quotient.mk _ x)) = _
    change integralCoefficientULift l E n (Ideal.Quotient.mk _ x) = _
    rw [hq]
    change ULift.up (Ideal.Quotient.mk _ x.down) =
      ULift.up ((Padic.coefficientExtensionTransition l E (n + 1))
        ((integralCoefficientULift l E (n + 1) (Ideal.Quotient.mk _ x)).down))
    rw [hq]
    rfl
  let c : adicLisseRingSystem T d.ideal ⋙ F ⟶
      WeilConjectures.integralCoefficientSheafSystem l E T :=
    NatTrans.ofOpSequence
      (fun n ↦ F.map (C.map (integralCoefficientULift l E n).toCommRingCatIso.hom))
      (by
        intro n
        dsimp only [Functor.comp_map]
        simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
          WeilConjectures.integralCoefficientSheafSystem,
          WeilConjectures.integralCoefficientSheafTransition]
        change F.map (C.map _) ≫ F.map (C.map _) =
          F.map (C.map _) ≫ F.map (C.map _)
        simp only [← F.map_comp, ← C.map_comp, htrans])
  have (n : ℕᵒᵖ) : IsIso (c.app n) := by
    change IsIso (F.map (C.map (integralCoefficientULift l E n.unop).toCommRingCatIso.hom))
    infer_instance
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have : PreservesLimit (pbcAdicRings T d) F := by
    have : PreservesLimit (pbcAdicRings T d)
        (F ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}) :=
      inferInstanceAs (PreservesLimit (pbcAdicRings T d)
        (sheafToPresheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
          (Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat.{u + 1} RingCat.{u + 1}).obj
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
    exact preservesLimit_of_reflects_of_preserves F
      (sheafToPresheaf (ProEt.topology T) RingCat.{u + 1})
  let w := Functor.isoWhiskerRight (pbcConstantSystemComparison T d).symm F ≪≫ asIso c
  let e := preservesLimitIso F (pbcAdicRings T d) ≪≫ HasLimit.isoOfNatIso w
  refine ⟨e, ?_, ?_⟩
  · intro n
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl
  · intro e' he'
    apply Iso.ext
    apply limit.hom_ext
    intro n
    change e'.hom ≫ limit.π _ n = e.hom ≫ limit.π _ n
    rw [he' n.unop]
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl

/-- Canonical ring comparison, chosen from its unique projection normalization.
Source: Bhatt--Scholze, Definition 6.5.1
(auxiliary; not a blueprint node). -/
def integralDetailedCoefficientComparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (integralDetailedCoefficientComparison_exists T l E).exists.choose

/-- Scalar restriction along this canonical ring isomorphism is exact.
Source: Bhatt--Scholze, Section 6.5; Stacks Tag 03DA
(auxiliary; not a blueprint node).
Proof: restriction changes only the scalar action. Restriction along the inverse
is its inverse equivalence. Finite limits and colimits are unchanged on underlying
additive sheaves, and therefore preserved. -/
theorem integralDetailedCoefficientRestriction_exact
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom) := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom
  let R := (adicLisseForget T).obj (pbcAdicCompletion T (pbcIntegralDatum l E))
  let B := WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} B))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} B))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)⟩

end AlgebraicGeometry.Scheme
