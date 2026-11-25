/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompleted
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
import all WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Mathlib.GroupTheory.OrderOfElement

/-!
# Bounded constructible derived-complete objects

Source: blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The coefficient ring is the actual inverse limit. The three defining conditions
are properties; no origin, local model, or completion representative is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The valuation ring in the small site's coefficient universe. ULift changes size
only. Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcIntegralRing := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)

/-- The recorded uniformizer, with the same harmless size lift.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcUniformizer : PbcIntegralRing l E := ULift.up (Padic.coefficientExtensionUniformizer l E)

/-- The finite-extension integer ring satisfies the recorded coefficient hypotheses.
This is proof data only; the ideal and quotient rings are the actual constructions.
Source: blueprint order 1300, coefficient convention; Serre, Local Fields II.2
(blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: the recorded integer ring is a DVR and its uniformizer generates its maximal
ideal. It is Noetherian and that principal ideal is finitely generated. Its finite
residue field has positive characteristic, hence every residue element has finite
additive order. Multiplication by each positive uniformizer power is injective; its
two-term finite-free resolution proves perfectness of the quotient. Positive quotients
are finite by finite_coefficientExtensionRing. Transport through the ULift ring
equivalence gives exactly the lifted ring, ideal powers and quotients displayed here. -/
theorem pbcCoefficientDatumProperties :
    IsNoetherianRing (PbcIntegralRing l E) ∧
      (Ideal.span ({pbcUniformizer l E} : Set (PbcIntegralRing l E))).FG ∧
      (∀ x : PbcIntegralRing l E ⧸ Ideal.span {pbcUniformizer l E},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (PbcIntegralRing l E)
        (Ideal.span {pbcUniformizer l E}) n) ∧
      ∀ n : ℕ, Finite (PbcIntegralRing l E ⧸
        (Ideal.span {pbcUniformizer l E}) ^ (n + 1)) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E :=
    ULift.ringEquiv
  let : IsPrincipalIdealRing (PbcIntegralRing l E) :=
    IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let : IsDomain (PbcIntegralRing l E) := e.toMulEquiv.isDomain _
  have hfinite (n : ℕ) : Finite (PbcIntegralRing l E ⧸
      (Ideal.span {pbcUniformizer l E}) ^ (n + 1)) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    have hI : Padic.coefficientExtensionIdeal l E (n + 1) =
        Ideal.map e.toRingHom ((Ideal.span {pbcUniformizer l E}) ^ (n + 1)) := by
      simp [Padic.coefficientExtensionIdeal, Ideal.map_pow, Ideal.map_span,
        Set.image_singleton, e, pbcUniformizer]
      rfl
    let eq := Ideal.quotientEquiv _ _ e hI
    exact Finite.of_equiv (Padic.coefficientExtensionRing l E (n + 1)) eq.symm.toEquiv
  refine ⟨inferInstance, Submodule.fg_span_singleton _, ?_, ?_, hfinite⟩
  · have : Finite (PbcIntegralRing l E ⧸ Ideal.span {pbcUniformizer l E}) := by
      simpa only [Nat.zero_add, pow_one] using hfinite 0
    intro x
    exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  · intro n _hn
    let R := PbcIntegralRing l E
    let J : Ideal R := (Ideal.span {pbcUniformizer l E}) ^ n
    let M := ModuleCat.of R (R ⧸ J)
    let q : ModuleCat.of R R ⟶ M := ModuleCat.ofHom J.mkQ
    have hq (x : R) : q x = 0 ↔ x ∈ Ideal.span {pbcUniformizer l E ^ n} := by
      change Ideal.Quotient.mk J x = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simp only [J, Ideal.span_singleton_pow]
    have hp : pbcUniformizer l E ≠ 0 := by
      intro hp
      apply AlgebraicGeometry.uniformizer_ne_zero l E
      exact congrArg ULift.down hp
    have : Mono (ModuleCat.ofHom (LinearMap.mulLeft R (pbcUniformizer l E ^ n))) := by
      rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      exact mul_left_cancel₀ (pow_ne_zero n hp) hxy
    have : Epi q := (ModuleCat.epi_iff_surjective q).2 J.mkQ_surjective
    obtain ⟨hw, hex⟩ := AlgebraicGeometry.principalExact (pbcUniformizer l E ^ n) M q hq
    obtain ⟨P, hge, hle, hfree, _, _, _, ε, hε, _, _⟩ :=
      AlgebraicGeometry.twoTermResolution (pbcUniformizer l E ^ n) M q hw hex
    let := HasDerivedCategory.standard (ModuleCat.{u + 1} R)
    let : QuasiIso ε := hε
    unfold adicQuotientPerfect
    refine ⟨P, -1, 0, hge, hle, ?_, ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩⟩
    intro i
    have := (hfree i).1
    exact ⟨inferInstance, (hfree i).2⟩

/-- The actual uniformizer-adic coefficient datum. All choices here are proofs of
properties of the already specified ring and ideal.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcIntegralDatum : AdicCoefficientDatum (PbcIntegralRing l E) where
  ideal := Ideal.span {pbcUniformizer l E}
  noetherian := (pbcCoefficientDatumProperties l E).1
  finitelyGenerated := (pbcCoefficientDatumProperties l E).2.1
  quotientTorsion := (pbcCoefficientDatumProperties l E).2.2.1
  quotientPerfect := (pbcCoefficientDatumProperties l E).2.2.2.1
  quotientFinite := (pbcCoefficientDatumProperties l E).2.2.2.2

end AlgebraicGeometry.Scheme
