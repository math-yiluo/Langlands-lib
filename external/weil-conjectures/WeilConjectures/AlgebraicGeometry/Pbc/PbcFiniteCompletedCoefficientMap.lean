/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink

/-!
# Finite extension maps of the actual completed PBC coefficient sheaves

## Main definitions

* `pbcIntegerInclusion`: the actual inclusion of lifted valuation rings.
* `pbcCompletedScalarMap`: the ring-sheaf map fixed by finite projections.
* `pbcAmbientScalarExtension`: the recorded K-flat derived tensor extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance 3000] WeilConjectures.sfAbBijective

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
/-- Finite-dimensional coefficient fields admit canonical models in the scheme universe. -/
instance pbcFiniteFieldSmall (E : Padic.FiniteCoefficientFields l Ω) : Small.{u} E.val :=
  Module.Finite.small.{u} (Padic l) E.val

/-- The coefficient field transported through the canonical shrink equivalence. -/
def pbcFiniteField (E : Padic.FiniteCoefficientFields l Ω) : Type u := Shrink.{u} E.val

/-- The single field structure transported to the canonical small coefficient model. -/
instance pbcFiniteFieldField (E : Padic.FiniteCoefficientFields l Ω) :
    Field (pbcFiniteField.{u} l Ω E) := inferInstanceAs (Field (Shrink.{u} E.val))

/-- The base-field algebra on the canonical small coefficient model. -/
instance pbcFiniteFieldAlgebra (E : Padic.FiniteCoefficientFields l Ω) :
    Algebra (Padic l) (pbcFiniteField.{u} l Ω E) :=
  inferInstanceAs (Algebra (Padic l) (Shrink.{u} E.val))

/-- Finiteness is unchanged by the canonical coefficient transport. -/
instance pbcFiniteFieldFinite (E : Padic.FiniteCoefficientFields l Ω) :
    FiniteDimensional (Padic l) (pbcFiniteField.{u} l Ω E) :=
  Module.Finite.equiv (Shrink.algEquiv (Padic l) E.val).symm.toLinearEquiv

/-- The existing adic datum on the canonically transported finite coefficient field. -/
abbrev pbcStageDatum (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)

/-- The existing uniformizer on the canonically transported coefficient field. -/
abbrev pbcStageUniformizer (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcUniformizer l (pbcFiniteField.{u} l Ω E)

variable {E F : Padic.FiniteCoefficientFields l Ω}

/-- The actual intermediate-field inclusion conjugated by the coefficient equivalences. -/
def pbcFiniteFieldInclusion (h : E ≤ F) :
    pbcFiniteField.{u} l Ω E →ₐ[Padic l] pbcFiniteField.{u} l Ω F :=
  (Shrink.algEquiv (Padic l) F.val).symm.toAlgHom.comp
    ((IntermediateField.inclusion h).comp (Shrink.algEquiv (Padic l) E.val).toAlgHom)

/-- The actual inclusion of integer rings, with the coefficient-size lift. -/
def pbcIntegerInclusion (h : E ≤ F) :
    PbcIntegralRing l (pbcFiniteField.{u} l Ω E) →+*
      PbcIntegralRing l (pbcFiniteField.{u} l Ω F) :=
  RingHom.ulift
    (WeilConjectures.integralScalarIntegerInclusion l
      (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion.{u} l Ω h))

-- Keep the existing algebraic-closure parameter in the public signature.
set_option linter.unusedSectionVars false in
/-- Integer inclusion preserves every power of the maximal ideal. -/
theorem pbcIntegerInclusion_ideal (h : E ≤ F) (n : ℕ) :
    (pbcStageDatum.{u} l Ω E).ideal ^ (n + 1) ≤
      Ideal.comap (pbcIntegerInclusion l Ω h) ((pbcStageDatum.{u} l Ω F).ideal ^ (n + 1)) := by
  intro x hx
  have hx' : x.down ∈ Padic.coefficientExtensionIdeal l
      (pbcFiniteField.{u} l Ω E) (n + 1) := by
    change x ∈ Ideal.span {pbcStageUniformizer.{u} l Ω E} ^ (n + 1) at hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have hxd := map_dvd
      (ULift.ringEquiv.toRingHom : PbcIntegralRing l (pbcFiniteField.{u} l Ω E) →+* _) hx
    rw [map_pow] at hxd
    exact hxd
  have hy := Ideal.Quotient.eq_zero_iff_mem.mp
    (WeilConjectures.integralScalar_quotient_kernel l
      (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) n x.down hx')
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hy
  change pbcIntegerInclusion l Ω h x ∈
    Ideal.span {pbcStageUniformizer.{u} l Ω F} ^ (n + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hy' := map_dvd
    (ULift.ringEquiv.symm.toRingHom : _ →+*
      PbcIntegralRing l (pbcFiniteField.{u} l Ω F)) hy
  rw [map_pow] at hy'
  exact hy'

/-- The quotient-ring map induced by integer inclusion at positive level n+1. -/
def pbcQuotientInclusion (h : E ≤ F) (n : ℕ) :=
  Ideal.Quotient.lift ((pbcStageDatum.{u} l Ω E).ideal ^ (n + 1))
    ((Ideal.Quotient.mk ((pbcStageDatum.{u} l Ω F).ideal ^ (n + 1))).comp
      (pbcIntegerInclusion l Ω h))
    (fun _x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
      (pbcIntegerInclusion_ideal l Ω h n hx))

variable (T : Scheme.{u})

/-- The coefficient map on the actual finite coefficient sheaves, through their
constant-section-normalized identifications. -/
def pbcFiniteScalarMap (h : E ≤ F) (n : ℕ) :
    (pbcAdicRings T (pbcStageDatum.{u} l Ω E)).obj (op n) ⟶
      (pbcAdicRings T (pbcStageDatum.{u} l Ω F)).obj (op n) :=
  (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).inv ≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (pbcQuotientInclusion l Ω h n)) ≫
    (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω F) n).hom

/-- The finite projections determine a unique map of completed coefficient sheaves. -/
theorem pbcCompletedScalarMap_exists (h : E ≤ F) :
    ∃! c : pbcAdicCompletion T (pbcStageDatum.{u} l Ω E) ⟶
        pbcAdicCompletion T (pbcStageDatum.{u} l Ω F),
      ∀ n : ℕ, c ≫ pbcAdicProjection T (pbcStageDatum.{u} l Ω F) n =
        pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n ≫ pbcFiniteScalarMap l Ω T h n := by
  let t : adicLisseRingSystem T (pbcStageDatum.{u} l Ω E).ideal ⟶
      adicLisseRingSystem T (pbcStageDatum.{u} l Ω F).ideal :=
    NatTrans.ofOpSequence (fun n ↦
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (pbcQuotientInclusion l Ω h n))) (fun n ↦ by
      simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext x
      rfl)
  let s : pbcAdicRings T (pbcStageDatum.{u} l Ω E) ⟶
      pbcAdicRings T (pbcStageDatum.{u} l Ω F) :=
    (pbcConstantSystemComparison T (pbcStageDatum.{u} l Ω E)).inv ≫ t ≫
      (pbcConstantSystemComparison T (pbcStageDatum.{u} l Ω F)).hom
  refine ⟨limMap s, ?_, ?_⟩
  · intro n
    exact limMap_π s (op n)
  · intro c hc
    apply limit.hom_ext
    intro n
    exact (hc n.unop).trans (limMap_π s n).symm

/-- The unique map into the completed coefficient ring fixed at every finite level. -/
def pbcCompletedScalarMap (h : E ≤ F) :
    pbcAdicCompletion T (pbcStageDatum.{u} l Ω E) ⟶
      pbcAdicCompletion T (pbcStageDatum.{u} l Ω F) :=
  (pbcCompletedScalarMap_exists l Ω T h).exists.choose

/-- The actual ambient K-flat derived tensor extension. -/
abbrev pbcAmbientScalarExtension (h : E ≤ F) :
    PbcCompletedDerived T (pbcStageDatum.{u} l Ω E) ⥤
      PbcCompletedDerived T (pbcStageDatum.{u} l Ω F) :=
  pbcDerivedExtend (pbcCompletedScalarMap l Ω T h)

end AlgebraicGeometry.Scheme
