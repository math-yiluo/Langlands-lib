/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationHomTransport
public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationDerivedHom
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Linear.Basic
import WeilConjectures.AlgebraicGeometry.Completed.CompletedContinuousHomHypotheses
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Constructible rational Hom comparison

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62
(blueprint: lem-per-constructible-rational-hom-comparison).

The completed integral category and the realization, including its normalized coefficient
maps, are the published ones. The general scalar-localization comparison predicate includes
all fraction, naturality, identity, composition and simultaneous-shift equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Specialize the existing fraction-normalized comparison to completed integral objects
and the actual derived scalar extension of a rational module realization. The existential
shift structure expresses commutation with shifts for this derived functor; the predicate
records the shift comparison explicitly in its fraction and compatibility formulas.
Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2)
(blueprint: lem-per-constructible-rational-hom-comparison). -/
def ConstructibleRationalHomComparison (R : RationalModuleRealization l E X) : Prop :=
  (fun [_localizedLinear : Linear (Localization.Away (pbcUniformizer l E))
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)))] ↦
    ∃ (_shift : (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion)).CommShift ℤ),
      scalarLocalizationHomComparison (PbcIntegralRing l E) (pbcUniformizer l E)
        (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion))
        (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
        (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)))
    (_localizedLinear := rationalRealizationLocalizedLinear l E X R)

attribute [local instance 2000] Linear.homModule

open scoped TensorProduct

private def postcompLinearEquiv (S : Type*) [CommRing S]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (K : D) {L M : D} (e : L ≅ M) : (K ⟶ L) ≃ₗ[S] (K ⟶ M) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp only [Preadditive.add_comp]
  map_smul' a f := by simp only [Linear.smul_comp, RingHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorHomEquivalences (A : Type*) [CommRing A] (t : A)
    {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasShift D ℤ]
    {T : Type*} [Category T] [Preadditive T]
    [Linear (Localization.Away t) T] [HasShift T ℤ]
    (F : D ⥤ T) [F.CommShift ℤ] (P : ObjectProperty D)
    (h : scalarLocalizationHomComparison A t F P P) :
    ∃ e : ∀ K L : P.FullSubcategory,
      (Localization.Away t ⊗[A] (K ⟶ L)) ≃ₗ[Localization.Away t]
        (F.obj K.obj ⟶ F.obj L.obj),
      ∀ (K L : P.FullSubcategory) (a : Localization.Away t) (f : K ⟶ L),
        e K L (a ⊗ₜ[A] f) = a • F.map f.hom := by
  obtain ⟨e, he, _⟩ := h
  let g (K L : P.FullSubcategory) :
      (K ⟶ L) ≃ₗ[A] (K.obj ⟶ L.obj⟦(0 : ℤ)⟧) :=
    (InducedCategory.homLinearEquiv (R := A)).trans
      (postcompLinearEquiv A K.obj ((shiftFunctorZero D ℤ).app L.obj).symm)
  let E (K L : P.FullSubcategory) :
      (Localization.Away t ⊗[A] (K ⟶ L)) ≃ₗ[Localization.Away t]
        (F.obj K.obj ⟶ F.obj L.obj) := by
    let : Module (Localization.Away t)
        (LocalizedModule.Away t (K.obj ⟶ L.obj⟦(0 : ℤ)⟧)) :=
      LocalizedModule.moduleOfIsLocalization
        (S := Submonoid.powers t) (T := Localization.Away t)
    exact ((g K L).baseChange A (Localization.Away t) _ _).trans
      ((IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
        (LocalizedModule.mkLinearMap (Submonoid.powers t)
          (K.obj ⟶ L.obj⟦(0 : ℤ)⟧))).equiv.trans
        ((e K.obj K.property L.obj L.property 0).trans
          (postcompLinearEquiv (Localization.Away t) (F.obj K.obj)
            ((shiftFunctorZero T ℤ).app (F.obj L.obj)))))
  refine ⟨E, ?_⟩
  intro K L a f
  have h₁ : E K L (1 ⊗ₜ[A] f) = F.map f.hom := by
    let : Module (Localization.Away t)
        (LocalizedModule.Away t (K.obj ⟶ L.obj⟦(0 : ℤ)⟧)) :=
      LocalizedModule.moduleOfIsLocalization
        (S := Submonoid.powers t) (T := Localization.Away t)
    let b := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) (K.obj ⟶ L.obj⟦(0 : ℤ)⟧))
    have hb := b.equiv_symm_apply (g K L f)
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
    rw [← hb, LinearEquiv.apply_symm_apply]
    change e K.obj K.property L.obj L.property 0
      (LocalizedModule.mk (g K L f) 1) ≫ (shiftFunctorZero T ℤ).hom.app _ = _
    have hn := he K.obj K.property L.obj L.property 0 (g K L f) 0
    simp only [pow_zero, one_smul] at hn
    change e K.obj K.property L.obj L.property 0
      (LocalizedModule.mk (g K L f) 1) = _ at hn
    rw [hn, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    change (F.map (f.hom ≫ (shiftFunctorZero D ℤ).inv.app L.obj) ≫
      F.map ((shiftFunctorZero D ℤ).hom.app L.obj) ≫
        (shiftFunctorZero T ℤ).inv.app (F.obj L.obj)) ≫
          (shiftFunctorZero T ℤ).hom.app (F.obj L.obj) = F.map f.hom
    simp only [Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [Category.comp_id, ← F.map_comp, Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [Category.comp_id]
  have ha : a ⊗ₜ[A] f = a • ((1 : Localization.Away t) ⊗ₜ[A] f) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, map_smul, h₁]

private theorem coefficient_map (a : PbcIntegralRing l E) :
    pbcRationalCoefficientEquiv l E
      (algebraMap _ (Localization.Away (pbcUniformizer l E)) a) = a.down.val := by
  dsimp [pbcRationalCoefficientEquiv]
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  exact ((Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose
    ).commutes a.down

private theorem coefficient_inversePower (n : ℕ) :
    pbcRationalCoefficientEquiv l E
      ((IsLocalization.Away.invSelf (pbcUniformizer l E) :
        Localization.Away (pbcUniformizer l E)) ^ n) =
      (((pbcUniformizer l E).down.val ^ n)⁻¹) := by
  have h := congrArg (pbcRationalCoefficientEquiv l E)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away (pbcUniformizer l E))
      (pbcUniformizer l E))
  rw [map_mul, map_one, coefficient_map] at h
  rw [map_pow, eq_inv_of_mul_eq_one_right h, inv_pow]

private theorem inversePower_eq_mk (A : Type*) [CommRing A] (t : A) (n : ℕ) :
    (IsLocalization.Away.invSelf t : Localization.Away t) ^ n =
      Localization.mk 1 (⟨t ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers t) := by
  rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  rw [map_pow, ← mul_pow, mul_comm (IsLocalization.Away.invSelf t),
    IsLocalization.Away.mul_invSelf, one_pow, map_one]

private theorem tensor_is_fraction (A : Type*) [CommRing A] (t : A)
    (M : Type*) [AddCommGroup M] [Module A M]
    (z : Localization.Away t ⊗[A] M) :
    ∃ (f : M) (n : ℕ),
      z = ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[A] f := by
  obtain ⟨x, rfl⟩ := (LocalizedModule.equivTensorProduct (Submonoid.powers t) M).surjective z
  induction x using LocalizedModule.induction_on with
  | _ f s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = ⟨t ^ n, ⟨n, rfl⟩⟩ := Subtype.ext hn.symm
    subst s
    exact ⟨f, n, by rw [LocalizedModule.equivTensorProduct_apply_mk,
      inversePower_eq_mk]⟩

private theorem fraction_tmul (A : Type*) [CommRing A]
    (C : Type*) [Category C] [Preadditive C] [Linear A C] (t : A)
    (K L : C) (f : K ⟶ L) (n : ℕ) :
    ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
        (ScalarLocalization.localization A C t).map f =
      ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[A] f := by
  change _ • ((1 : Localization.Away t) ⊗ₜ[A] f) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

open Classical in
omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem homContinuous_of_sums
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
    (h : ∀ (I : Type (u + 1)) [Countable I]
      (M : I → PbcCompletedDerived X (pbcIntegralDatum l E)),
      (∃ n : ℤ, ∀ i : I, (M i).IsGE n) →
      ∀ (q : ℤ) (s : Cofan M), IsColimit s →
        Function.Bijective
          (DirectSum.toModule (PbcIntegralRing l E) I (K.obj ⟶ s.pt⟦q⟧)
            (fun i : I ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
              ((shiftFunctor _ q).map (s.inj i))))) :
    DerivedCategory.CountableBoundedBelowHomContinuous K.obj := by
  classical
  intro M b hb B ι hc q
  let : DecidableEq (ULift.{u + 1} ℕ) := fun a b ↦ Classical.propDecidable (a = b)
  let e : ULift.{u + 1} ℕ ≃ ℕ := Equiv.ulift
  let s : Cofan (fun i : ULift.{u + 1} ℕ ↦ M i.down) := Cofan.mk B (fun i ↦ ι i.down)
  have hs : IsColimit s := (Cofan.isColimitEquivOfEquiv e (Cofan.mk B ι)) hc
  have hU := h (ULift.{u + 1} ℕ) (fun i ↦ M i.down) ⟨b, fun i ↦ hb i.down⟩ q s hs
  let a := DirectSum.equivCongrLeft (β := fun i : ULift.{u + 1} ℕ ↦
    K.obj ⟶ (M i.down)⟦q⟧) e
  let f := DirectSum.toAddMonoid (fun n : ℕ ↦ Preadditive.rightComp K.obj ((ι n)⟦q⟧'))
  let g := (DirectSum.toModule (PbcIntegralRing l E) (ULift.{u + 1} ℕ)
    (K.obj ⟶ B⟦q⟧) (fun i ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
      ((ι i.down)⟦q⟧'))).toAddMonoidHom
  have heq : f.comp a.toAddMonoidHom = g := by
    apply DirectSum.addHom_ext
    intro i v
    rcases i with ⟨i⟩
    simp only [AddMonoidHom.comp_apply]
    change f (a (DirectSum.of _ (e.symm i) v)) = _
    rw [DirectSum.equivCongrLeft_of]
    change f (DirectSum.of _ i v) = g (DirectSum.of _ ⟨i⟩ v)
    rw [show f = DirectSum.toAddMonoid
      (fun n : ℕ ↦ Preadditive.rightComp K.obj ((ι n)⟦q⟧')) from rfl]
    rw [DirectSum.toAddMonoid_of]
    change _ = (DirectSum.toModule (PbcIntegralRing l E) (ULift.{u + 1} ℕ)
      (K.obj ⟶ B⟦q⟧) (fun j ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
        ((ι j.down)⟦q⟧'))) (DirectSum.lof (PbcIntegralRing l E) _ _ ⟨i⟩ v)
    rw [DirectSum.toModule_lof]
    rfl
  have hcomp : Function.Bijective (f.comp a.toAddMonoidHom) := by
    rw [heq]
    exact hU
  exact ⟨fun x y hxy ↦ by
    obtain ⟨x, rfl⟩ := a.surjective x
    obtain ⟨y, rfl⟩ := a.surjective y
    exact congrArg a (hcomp.injective hxy), fun y ↦ by
      obtain ⟨x, hx⟩ := hcomp.surjective y
      exact ⟨a x, hx⟩⟩

open Classical in
/-- Constructible completed integral objects satisfy the countable, uniformly bounded-below
coproduct-Hom comparison. Actual scalar extension therefore identifies every localized
shifted Hom with its rational ambient Hom, naturally and compatibly with identities,
composition and shifts. The specified realization of the raw rationalization is full
and faithful into the actual ambient derived category.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62
(blueprint: lem-per-constructible-rational-hom-comparison).

Proof:
1. Choose a rational realization and apply completedContinuousHomHypotheses. Its
comparison field gives the first conjunct. Reindex its direct-sum comparison along
ULift ℕ ≃ ℕ to obtain sequential bounded-below Hom continuity. Its boundedness field
provides a lower cohomological bound for each integral object.
2. Apply rationalRealizationHomTransport to the specified realization and restrict
its general source and target predicates using step 1. Retain all five fraction
and coherence equations, giving ConstructibleRationalHomComparison.
3. At degree zero, the zero-shift isomorphism and the localized-module base-change
isomorphism identify the comparison with a linear equivalence on tensor Homs.
Conjugate by R.objects. Every localized tensor Hom has a fraction presentation.
The canonical coefficient equivalence sends inverse uniformizer powers to the
corresponding inverse powers in E. Therefore R.fractions identifies R.J.map with
this linear equivalence on every arrow. Its surjectivity and injectivity give
fullness and faithfulness. -/
theorem constructibleRationalHomComparison :
    (∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (I : Type (u + 1)) [Countable I]
      (M : I → PbcCompletedDerived X (pbcIntegralDatum l E)),
      (∃ n : ℤ, ∀ i : I, (M i).IsGE n) →
      ∀ (q : ℤ) (s : Cofan M), IsColimit s →
        Function.Bijective
          (DirectSum.toModule (PbcIntegralRing l E) I (K.obj ⟶ s.pt⟦q⟧)
            (fun i : I ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
              ((shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) q).map
                (s.inj i))))) ∧
    ∀ R : RationalModuleRealization l E X,
      ConstructibleRationalHomComparison l E X R ∧ R.J.Full ∧ R.J.Faithful := by
  classical
  obtain ⟨R₀⟩ := rationalModuleRealizationFunctor l E X
  obtain ⟨H₀⟩ := completedContinuousHomHypotheses l E X R₀
  have hsum : ∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (I : Type (u + 1)) [Countable I]
      (M : I → PbcCompletedDerived X (pbcIntegralDatum l E)),
      (∃ n : ℤ, ∀ i : I, (M i).IsGE n) →
      ∀ (q : ℤ) (s : Cofan M), IsColimit s →
        Function.Bijective
          (DirectSum.toModule (PbcIntegralRing l E) I (K.obj ⟶ s.pt⟦q⟧)
            (fun i : I ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
              ((shiftFunctor _ q).map (s.inj i)))) := by
    intro K I _ M hM q s hs
    let t := Cofan.mk ((completedContinuousTransport l E X R₀).obj s.pt)
      (fun i ↦ (completedContinuousTransport l E X R₀).map (s.inj i))
    obtain ⟨ht⟩ := H₀.coproducts I M s hs
    obtain ⟨c, _, φ, ψ, _, _, _, h, _⟩ := H₀.comparison K I M hM q s hs t ht
    exact h
  refine ⟨hsum, fun R ↦ ?_⟩
  let := R.moduleLinear
  let := R.additive
  let := R.linear
  let := rationalRealizationLocalizedLinear l E X R
  obtain ⟨shift, hgeneral⟩ := rationalRealizationHomTransport l E X R
  let := shift
  have hcontinuous : ∀ K, PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K →
      DerivedCategory.CountableBoundedBelowHomContinuous K := by
    intro K hK
    exact homContinuous_of_sums l E X ⟨K, hK⟩ (hsum ⟨K, hK⟩)
  have hbounded : ∀ K, PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K →
      ∃ b : ℤ, K.IsGE b := by
    intro K hK
    obtain ⟨a, b, _, ha, _⟩ := H₀.bounded ⟨K, hK⟩
    exact ⟨a, ha⟩
  obtain ⟨e, hn, hnat, hid, hcomp, hshift⟩ := hgeneral
  have hcomparison : scalarLocalizationHomComparison (PbcIntegralRing l E)
      (pbcUniformizer l E) (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion))
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) := by
    refine ⟨fun K hK L hL q ↦ e K (hcontinuous K hK) L (hbounded L hL) q,
      ?_, ?_, ?_, ?_, ?_⟩
    · intros; apply hn
    · intros; apply hnat
    · intros; apply hid
    · intros; apply hcomp
    · intros; apply hshift
  refine ⟨⟨shift, hcomparison⟩, ?_⟩
  obtain ⟨ε, hε⟩ := tensorHomEquivalences (PbcIntegralRing l E)
    (pbcUniformizer l E) (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion))
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) hcomparison
  let η (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :=
    (ε K L).trans (Linear.homCongr (Localization.Away (pbcUniformizer l E))
      (eqToIso (R.objects K).symm) (eqToIso (R.objects L).symm))
  have hmap (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (z : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K ⟶
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj L) :
      R.J.map z = η K L z := by
    obtain ⟨f, n, rfl⟩ := tensor_is_fraction (PbcIntegralRing l E)
      (pbcUniformizer l E) (K ⟶ L) z
    have hcoef := coefficient_inversePower l E n
    have hsymm : (pbcRationalCoefficientEquiv l E).symm
        (((pbcUniformizer l E).down.val ^ n)⁻¹) =
        (IsLocalization.Away.invSelf (pbcUniformizer l E) :
          Localization.Away (pbcUniformizer l E)) ^ n := by
      rw [← hcoef, RingEquiv.symm_apply_apply]
    have hfrac := R.fractions K L f n
    rw [hsymm] at hfrac
    have hinput := fraction_tmul (PbcIntegralRing l E)
      (PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (pbcUniformizer l E) K L f n
    rw [hinput] at hfrac
    rw [hfrac]
    dsimp only [η, LinearEquiv.trans_apply]
    rw [hε, Linear.homCongr_apply]
    change eqToHom (R.objects K) ≫
      ((((pbcUniformizer l E).down.val ^ n)⁻¹) •
        (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion)).map f.hom) ≫
        eqToHom (R.objects L).symm =
      (eqToHom (R.objects K) ≫
        (pbcRationalCoefficientEquiv l E
          ((IsLocalization.Away.invSelf (pbcUniformizer l E) :
            Localization.Away (pbcUniformizer l E)) ^ n) •
            (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion)).map f.hom)) ≫
        eqToHom (R.objects L).symm
    rw [hcoef, Category.assoc]
  constructor
  · exact ⟨fun {K L} ↦ by
      rcases K with ⟨K⟩
      rcases L with ⟨L⟩
      change Function.Surjective (fun z ↦ R.J.map z)
      intro f
      obtain ⟨z, hz⟩ := (η K L).surjective f
      exact ⟨z, (hmap K L z).trans hz⟩⟩
  · exact ⟨fun {K L} ↦ by
      rcases K with ⟨K⟩
      rcases L with ⟨L⟩
      change Function.Injective (fun z ↦ R.J.map z)
      intro f g hfg
      apply (η K L).injective
      exact (hmap K L f).symm.trans (hfg.trans (hmap K L g))⟩

end AlgebraicGeometry.Scheme
