/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackIso
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Continuous coefficient sheaves and immersion restriction

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.5.8(1), Definition 6.8.1,
Lemma 6.8.2 and the paragraph preceding Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Scheme

/-- Canonical completion, localization and immersion restriction of continuous coefficients.
The residue comparisons preserve constant sections; the completion comparison reduces
functions pointwise. The localization comparison is fixed on all integral numerators.
The immersion comparisons have the continuous-function pullback adjuncts. The last two
clauses are equalities of sheaf maps expressing coefficient and composition compatibility.
Source: Bhatt--Scholze, Lemmas 4.2.12, 6.5.8(1), Definition 6.8.1, Lemma 6.8.2(1),(2)
and paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction).

Proof, following the node's six steps:
1. Continuous abelian functions satisfy fpqc descent
(`lem-cbc-continuous-functions-fpqc-sheaf`). Pro-etale coverings are fpqc coverings;
pointwise operations and the underlying-set criterion
(`situation-conventions`) give ring sheaves.
2. For each discrete quotient, glue constants on the open fibres of a continuous function.
Open immersions and their composites are weakly etale
(`lem-weil-proetale-weakly-etale-localization`), and affine quasi-compactness verifies
these fibre covers are site coverings. This gives the constant-sheaf universal property
(`def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`), preserving constants.
3. Compute limits sectionwise (`def-pur-sheaf-inverse-limit`). Compatible residues lift
pointwise to a unique element of the complete valuation ring
(`lem-weil-l-adic-extension-complete`, `lem-weil-l-adic-extension-integers-dvr`).
The congruence cosets form an open neighbourhood basis, so the lift is continuous.
Reduction and lifting are inverse ring maps and commute with restriction.
4. The fraction map is injective pointwise. A continuous rational function is integral
after multiplication by a power of the uniformizer on each member of its open denominator
cover. These opens are site objects and a site cover by step 2. Their fractions agree;
sheafification gives the inverse. The DVR decomposition of ℓ as a unit times a positive
power of the uniformizer identifies this localization with that of Lemma 6.8.2(2).
5. A locally closed immersion into a noetherian scheme is constructible. Apply
`lem-weil-pbc-proetale-immersion-limit-preservation` to the residue tower, then
`prop-weil-pbc-proetale-constant-ring-map` to each finite discrete quotient (finite by
`lem-weil-valued-dvr-finite-quotients`). The resulting limit map is precomposition after
every residue projection and hence is precisely the normalized integral comparison.
6. Ring-sheaf inverse image (`def-weil-proetale-inverse-image`) commutes with localization
by its adjunction and the localization universal property. This gives rational restriction.
Integral inclusion and fractions commute with precomposition, proving the coefficient
square. Successive precomposition equals composite precomposition; after the canonical
inverse-image composition comparison the integral maps agree on every residue, and the
rational maps agree by localization. Thus both composition equations hold. -/
theorem continuousCoefficientImmersionRestriction (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    {Z : Scheme.{u}} (h : Z ⟶ X) [AlgebraicGeometry.IsImmersion h] :
    ∃ (i : integralCoefficientSheaf l X E ≅ finiteCoefficientLimit l X E)
      (b : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E)
      (cA : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (integralCoefficientSheaf l X E) ≅ integralCoefficientSheaf l Z E)
      (cE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l X E) ≅ rationalCoefficientSheaf l Z E),
      (∀ n : ℕ, ∃ q : (CategoryTheory.constantSheaf (ProEt.topology X)
          CommRingCat.{u + 1}).obj (finiteCoefficientRing l E n) ≅
          finiteContinuousCoefficientSheaf l X E n,
        (∀ (U : X.ProEtᵒᵖ) (a : finiteCoefficientRing l E n) (x : U.unop.left),
          finiteContinuousCoefficientValue l E X n U
            (q.hom.hom.app U ((CategoryTheory.toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app U a)) x = a) ∧
        (∀ (U : X.ProEtᵒᵖ)
          (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
          (finiteContinuousCoefficientValue l E X n U
            ((i.hom ≫ CategoryTheory.Limits.limit.π (finiteCoefficientTower l X E)
              (Opposite.op n) ≫ q.hom).hom.app U s) x).down =
                Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
                  (integralCoefficientValue l E X U s x))) ∧
      integralCoefficientLocalizationNormalized l E X b.hom ∧
      integralCoefficientRestrictionNormalized l E h cA.hom ∧
      rationalCoefficientRestrictionNormalized l E h cE.hom ∧
      (∃ (aX : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E)
        (aZ : integralCoefficientSheaf l Z E ⟶ rationalCoefficientSheaf l Z E),
        integralRationalCoefficientNormalized l E X aX ∧
        integralRationalCoefficientNormalized l E Z aZ ∧
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map aX ≫ cE.hom =
          cA.hom ≫ aZ) ∧
      (∀ (W : Scheme.{u}) (k : W ⟶ Z) [AlgebraicGeometry.IsImmersion k],
        ∃ (dA : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj
            (integralCoefficientSheaf l Z E) ≅ integralCoefficientSheaf l W E)
          (dE : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Z E) ≅ rationalCoefficientSheaf l W E)
          (eA : (proEtaleSheafInverseImage (k ≫ h) CommRingCat.{u + 1}).obj
            (integralCoefficientSheaf l X E) ≅ integralCoefficientSheaf l W E)
          (eE : (proEtaleSheafInverseImage (k ≫ h) CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l X E) ≅ rationalCoefficientSheaf l W E),
          integralCoefficientRestrictionNormalized l E k dA.hom ∧
          rationalCoefficientRestrictionNormalized l E k dE.hom ∧
          integralCoefficientRestrictionNormalized l E (k ≫ h) eA.hom ∧
          rationalCoefficientRestrictionNormalized l E (k ≫ h) eE.hom ∧
          eA.hom = (proEtaleRingInverseImageComp k h).hom.app
            (integralCoefficientSheaf l X E) ≫
              (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map cA.hom ≫ dA.hom ∧
          eE.hom = (proEtaleRingInverseImageComp k h).hom.app
            (rationalCoefficientSheaf l X E) ≫
              (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map cE.hom ≫ dE.hom) := by
  let := coefficientExtensionNormedField l E
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let K := ULift.{u + 1, u} E
  obtain ⟨i, hi⟩ := continuousCoefficientCompletion l E X
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  obtain ⟨hA, hE⟩ := continuousCoefficientPullback_isIso l E X h
  let := hA
  let := hE
  refine ⟨i, b, asIso (continuousCoefficientPullback A h),
    asIso (continuousCoefficientPullback K h), hi, hb,
    continuousCoefficientPullback_normalized A h,
    continuousCoefficientPullback_normalized K h, ?_, ?_⟩
  · refine ⟨integralRationalCoefficientMap l E X, integralRationalCoefficientMap l E Z,
      integralRationalCoefficientMap_normalized l E X,
      integralRationalCoefficientMap_normalized l E Z, ?_⟩
    exact continuousCoefficientPullback_naturality
      (RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype)
      (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)) h
  · intro W k _
    obtain ⟨heA, heE⟩ := continuousCoefficientPullback_isIso l E X (k ≫ h)
    let := heA
    let := heE
    have hdA : IsIso (continuousCoefficientPullback A k) := by
      have hc : IsIso ((proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (continuousCoefficientPullback A h) ≫ continuousCoefficientPullback A k) := by
        have hh := continuousCoefficientPullback_comp A k h
        have : IsIso ((proEtaleRingInverseImageComp k h).hom.app
            (continuousCoefficientSheaf X A) ≫
              ((proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
                (continuousCoefficientPullback A h) ≫ continuousCoefficientPullback A k)) := by
          rw [← hh]
          infer_instance
        exact IsIso.of_isIso_comp_left
          ((proEtaleRingInverseImageComp k h).hom.app (continuousCoefficientSheaf X A))
          _
      exact IsIso.of_isIso_comp_left
        ((proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (continuousCoefficientPullback A h)) (continuousCoefficientPullback A k)
    have hdE : IsIso (continuousCoefficientPullback K k) := by
      have hc : IsIso ((proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (continuousCoefficientPullback K h) ≫ continuousCoefficientPullback K k) := by
        have hh := continuousCoefficientPullback_comp K k h
        have : IsIso ((proEtaleRingInverseImageComp k h).hom.app
            (continuousCoefficientSheaf X K) ≫
              ((proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
                (continuousCoefficientPullback K h) ≫ continuousCoefficientPullback K k)) := by
          rw [← hh]
          infer_instance
        exact IsIso.of_isIso_comp_left
          ((proEtaleRingInverseImageComp k h).hom.app (continuousCoefficientSheaf X K))
          _
      exact IsIso.of_isIso_comp_left
        ((proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (continuousCoefficientPullback K h)) (continuousCoefficientPullback K k)
    let := hdA
    let := hdE
    exact ⟨asIso (continuousCoefficientPullback A k),
      asIso (continuousCoefficientPullback K k),
      asIso (continuousCoefficientPullback A (k ≫ h)),
      asIso (continuousCoefficientPullback K (k ≫ h)),
      continuousCoefficientPullback_normalized A k,
      continuousCoefficientPullback_normalized K k,
      continuousCoefficientPullback_normalized A (k ≫ h),
      continuousCoefficientPullback_normalized K (k ≫ h),
      continuousCoefficientPullback_comp A k h, continuousCoefficientPullback_comp K k h⟩

end AlgebraicGeometry.Scheme
