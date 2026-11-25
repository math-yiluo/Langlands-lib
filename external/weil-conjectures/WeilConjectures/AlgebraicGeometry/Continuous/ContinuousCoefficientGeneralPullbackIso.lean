/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackIso

/-! # Continuous coefficient pullback for arbitrary scheme morphisms

Source: Bhatt--Scholze, Lemma 4.2.12 and Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-coefficient-general-pullback-isIso)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Scheme

/-- Evaluation detects equality of rational coefficient sections.
Source: Bhatt--Scholze, Definition 6.8.1.
(blueprint: lem-weil-pbc-continuous-coefficient-general-pullback-isIso) -/
theorem rationalCoefficientValue_ext (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (V : X.ProEtᵒᵖ)
    (a b : (rationalCoefficientSheaf l X E).obj.obj V)
    (hab : ∀ x, rationalCoefficientValue l E X V a x =
      rationalCoefficientValue l E X V b x) : a = b := by
  letI := coefficientExtensionNormedField l E
  apply ContinuousMap.ext
  intro x
  exact ULift.down_injective (hab x)

/-- Continuous precomposition for the spectral norm, with the original field structure.
Source: Bhatt--Scholze, Definition 6.8.1.
(blueprint: lem-weil-pbc-continuous-coefficient-general-pullback-isIso) -/
noncomputable def rationalContinuousPullback
    (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l Z E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) h

/-- The spectral precomposition map has its specified adjunct.
Source: Bhatt--Scholze, Definition 6.8.1.
(blueprint: lem-weil-pbc-continuous-coefficient-general-pullback-isIso) -/
theorem rationalContinuousPullback_normalized
    (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    rationalCoefficientRestrictionNormalized l E h (rationalContinuousPullback l E h) := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback_normalized (ULift.{u + 1, u} E) h

/-- The normalized integral and rational continuous coefficient pullbacks are
isomorphisms along every scheme morphism.
Source: Bhatt--Scholze, Lemma 4.2.12 and Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-coefficient-general-pullback-isIso)

Proof. The finite constant quotient tower is preserved by inverse image, and
its limit is the continuous integral coefficient sheaf. Projectionwise reduction
identifies its comparison with the canonical pullback. To obtain a rational
inverse, pull back integral inclusion through the integral inverse. Constants
show that this map inverts the uniformizer. The localization universal property
extends it uniquely to rational coefficients. Naturality of inclusion and
uniqueness on integral numerators prove the two inverse equations. -/
theorem continuousCoefficientPullback_isIso_of_finiteExtension
    (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    letI := coefficientExtensionNormedField l E
    IsIso (continuousCoefficientPullback
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h) ∧
    IsIso (continuousCoefficientPullback (ULift.{u + 1, u} E) h) := by
  let := coefficientExtensionNormedField l E
  have hA := integralPullback_isIso l E h
  let := hA
  refine ⟨hA, ?_⟩
  let A := Padic.coefficientExtensionIntegers l E
  let T := ULift.{u + 1, u} A
  let K := ULift.{u + 1, u} E
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  let aX := integralRationalCoefficientMap l E X
  let aZ := integralRationalCoefficientMap l E Z
  let cA := asIso (continuousCoefficientPullback T h)
  let cE := continuousCoefficientPullback K h
  let g : integralCoefficientSheaf l Z E ⟶ L.obj (rationalCoefficientSheaf l X E) :=
    cA.inv ≫ L.map aX
  let inc : T →+* K := RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype
  have hinc : Continuous inc :=
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)
  let c0A := proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of T)
  let c0K := proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of K)
  let := constantRing_isIso h (CommRingCat.of T)
  let := constantRing_isIso h (CommRingCat.of K)
  let mK := (asIso c0K).inv ≫ L.map (continuousCoefficientConstantComparison X K)
  have hn : L.map ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom inc)) = c0A ≫
        (constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom inc) ≫ (asIso c0K).inv := by
    apply (cancel_mono c0K).mp
    have hinv : (asIso c0K).inv ≫ c0K = 𝟙 _ := (asIso c0K).inv_hom_id
    rw [Category.assoc, Category.assoc, hinv, Category.comp_id]
    exact proEtaleConstantInverseImageMap_naturality h (CommRingCat.ofHom inc)
  have hgconst : continuousCoefficientConstantComparison Z T ≫ g =
      (constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom inc) ≫ mK := by
    apply (cancel_epi c0A).mp
    calc
      _ = (L.map (continuousCoefficientConstantComparison X T) ≫ cA.hom) ≫ g := by
        exact (Category.assoc c0A (continuousCoefficientConstantComparison Z T) g).symm.trans
          (congrArg (fun q ↦ q ≫ g) (constantComparison_pullback T h).symm)
      _ = L.map (continuousCoefficientConstantComparison X T ≫ aX) := by
        simp only [g, Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp]
      _ = L.map ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom inc) ≫ continuousCoefficientConstantComparison X K) := by
        exact congrArg L.map (constantComparison_map inc hinc X).symm
      _ = _ := by rw [L.map_comp, hn]; simp [mK, Category.assoc]
  have hs := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm0 : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    hs.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A) =
      Padic.coefficientExtensionMaximalIdeal l E := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let t : T := ULift.up (Padic.coefficientExtensionUniformizer l E)
  have ht : inc t ≠ 0 := by
    intro hz
    apply hm0
    have hp : Padic.coefficientExtensionUniformizer l E = 0 := by
      apply Subtype.ext
      exact congrArg ULift.down hz
    rw [← hgen, hp, Ideal.span_singleton_zero]
  have hgunit : ∀ U : Z.ProEtᵒᵖ,
      IsUnit (g.hom.app U (ContinuousMap.const U.unop.left t)) := by
    intro U
    let ηA := toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj
      (CommRingCat.of T))
    let ηK := toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj
      (CommRingCat.of K))
    have hc : (continuousCoefficientConstantComparison Z T).hom.app U (ηA.app U t) =
        ContinuousMap.const U.unop.left t := by
      have hh := Equiv.apply_symm_apply
        ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
          ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of T))
          (continuousCoefficientSheaf Z T)) (continuousCoefficientConstants Z T)
      exact congrArg (fun q ↦ q.app U t) hh
    have hi : ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom inc)).hom.app U (ηA.app U t) = ηK.app U (inc t) := by
      have hh := (toSheafification (ProEt.topology Z) CommRingCat.{u + 1}).naturality
        ((Functor.const Z.ProEtᵒᵖ).map (CommRingCat.ofHom inc))
      exact (congrArg (fun q ↦ q.app U t) hh).symm
    have hu := congrArg (fun q ↦ q.hom.app U (ηA.app U t)) hgconst
    change g.hom.app U ((continuousCoefficientConstantComparison Z T).hom.app U
      (ηA.app U t)) = mK.hom.app U _ at hu
    have hu' : g.hom.app U (ContinuousMap.const U.unop.left t) =
        mK.hom.app U (ηK.app U (inc t)) :=
      (congrArg (g.hom.app U) hc).symm.trans (hu.trans (congrArg (mK.hom.app U) hi))
    exact hu'.symm ▸
      (((isUnit_iff_ne_zero.mpr ht).map (ηK.app U).hom).map (mK.hom.app U).hom)
  obtain ⟨v, hv⟩ := rationalLift l E Z (L.obj (rationalCoefficientSheaf l X E)) g hgunit
  have hnat : L.map aX ≫ cE = cA.hom ≫ aZ :=
    continuousCoefficientPullback_naturality inc hinc h
  have hright : v ≫ cE = 𝟙 (rationalCoefficientSheaf l Z E) := by
    apply rationalMap_ext l E Z
    change aZ ≫ (v ≫ cE) = aZ ≫ 𝟙 _
    rw [← Category.assoc, hv]
    simp only [g, Category.assoc, hnat, Iso.inv_hom_id_assoc, Category.comp_id]
  have haX : Epi aX := ⟨by
    intro G f g hh
    exact rationalMap_ext l E X f g hh⟩
  let := haX
  let := Functor.preservesEpimorphisms_of_adjunction
    (proEtaleSheafAdjunction h CommRingCat.{u + 1})
  have hleft : cE ≫ v = 𝟙 (L.obj (rationalCoefficientSheaf l X E)) := by
    apply (cancel_epi (L.map aX)).mp
    rw [← Category.assoc, hnat, Category.assoc, hv]
    simp [g]
  exact ⟨v, hleft, hright⟩

/-- The spectral rational coefficient pullback is invertible.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2.
(blueprint: lem-weil-pbc-continuous-coefficient-general-pullback-isIso)
Proof: apply the preceding finite-extension pullback theorem to the spectral norm. -/
instance rationalContinuousPullback_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X) : IsIso (rationalContinuousPullback l E h) :=
  (continuousCoefficientPullback_isIso_of_finiteExtension l E h).2

end AlgebraicGeometry.Scheme
