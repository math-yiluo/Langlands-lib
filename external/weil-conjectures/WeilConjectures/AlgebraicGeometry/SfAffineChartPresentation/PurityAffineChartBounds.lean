/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

set_option linter.privateModule false

/-!
# Affine-chart assembly for constructible exceptional inverse image
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

open Classical in
open Classical in
open Classical in
private theorem coefficient_killed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
  let h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hl : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    have he := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change Padic.coefficientExtensionAbsoluteValue l E
      (algebraMap ℚ_[l] E (l : ℚ_[l])) = ‖(l : ℚ_[l])‖ at he
    rw [map_natCast] at he
    rw [he]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rw [← hgen] at hl
  have hq := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hl n)
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hq

private theorem finite_dimension_bound {k : Type u} [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    topologicalKrullDim X ≤
      (((topologicalKrullDim X).unbotD 0).toNat : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  generalize topologicalKrullDim X = t at *
  induction t using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe t =>
    induction t using ENat.recTopCoe with
    | top => exact False.elim ((ENat.natCast_ne_top d)
        (top_le_iff.mp (WithBot.coe_le_coe.mp hd)))
    | coe t => simp

private theorem datum_charP (F : WeilConjectures.FiniteFieldDatum.{u}) : CharP F.k F.p := by
  classical
  let : Fintype F.k₀ := Fintype.ofFinite F.k₀
  let : Fact F.p.Prime := ⟨F.prime⟩
  let : CharP F.k₀ F.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, F.card_base, F.cardinality_eq])
  exact charP_of_injective_algebraMap (algebraMap F.k₀ F.k).injective F.p

private theorem coefficient_invertible
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k)) :
    HasInvertibleExponent
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y := by
  let := datum_charP F
  have hlk : (l : F.k) ≠ 0 := by
    intro h
    exact hl ((Nat.prime_dvd_prime_iff_eq F.prime (Fact.out : l.Prime)).mp
      ((CharP.cast_eq_zero_iff F.k F.p l).mp h)).symm
  have hu : IsUnit ((l ^ n : ℕ) : Γ(Y, ⊤)) := by
    have h := ((Ne.isUnit hlk).pow n).map (Scheme.ΓSpecIso (.of F.k)).inv.hom
    simpa only [← Nat.cast_pow, map_natCast] using h.map aY.appTop.hom
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, ?_, hu⟩
  apply ULift.down_injective
  change ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0
  exact coefficient_killed l E n

end AlgebraicGeometry.Scheme
