/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra

/-!
# Cohomological smoothness in finite-coefficient comparison coordinates

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-purity-conv,
proposition-exceptional-inverse-image-smooth-morphism, clauses 1--3 (blueprint:
proposition-exceptional-inverse-image-smooth-morphism).

This is the constructible pro-etale definition in etale-origin coordinates. The dualizing
object is comparison pullback of the etale dualizing object. Tensor and base-change maps
are comparison pullbacks of the specified counit mates, not arbitrary endpoint maps.
Every pro-etale Dctf object has an etale origin, so testing all etale representatives
whose images are Dctf tests precisely the original domain, independently of witnesses.
Comparison is fully faithful and monoidal on these objects. Its canonical unit, tensor,
pullback and compact-support comparisons identify these maps with the two transposes
in the node. Thus this uses the transported constructible adjunction, rather than an
ambient pro-etale adjunction. The legacy module imports two incompatible versions of
the inverse-image API; this module uses the published canonical etale maps directly.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the actual coefficient quotient, including its size lift.
Source: blueprint finite purity conventions (blueprint:
proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable instance finiteComparedCoefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The existing Nagata compactification in the finite-type field setting.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, separated finite-type
setting (blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def finiteComparedCompactification (P : PurityFiniteSetting.{u})
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f]
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    (aY : Y ⟶ AlgebraicGeometry.Spec (.of P.field.k))
    [AlgebraicGeometry.LocallyOfFiniteType aY] [AlgebraicGeometry.QuasiCompact aY] :
    AlgebraicGeometry.Compactification f :=
  letI := AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian aY
  letI := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace aY
  AlgebraicGeometry.HasCompactification.compactification f

/-- The coefficient hypothesis of finite purity supplies an invertible exponent on every
scheme over the fixed field; no divisibility of the level by the ramification index is needed.
Source: main-20261015, sk-def-purity-conv/def-pur-co-smoothness, finite coefficients
and the clause that ell is invertible on the schemes in sight
(blueprint: proposition-exceptional-inverse-image-smooth-morphism).
Proof: write ell for the coefficient prime and n for the positive level. In the DVR O_E,
ell lies in the maximal ideal (varpi_E): its spectral absolute value restricts to the
ell-adic one, in which ell has norm less than one. Consequently ell^n lies in (varpi_E)^n,
so its image in A = O_E/(varpi_E^n), and in the specified ULift, is zero. The integer
ell^n is positive. The finite field k_0 has characteristic p, as does its algebraic
closure k; since ell and p are distinct primes, ell^n is nonzero and hence a unit in k.
Map this unit through the spectrum global-sections identification and the structure
morphism to Gamma(T, top). These witnesses give HasInvertibleExponent. This argument
also applies to the empty scheme and does not require T to be finite type or separated. -/
theorem finiteComparedInvertibleExponent (P : PurityFiniteSetting.{u})
    {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ AlgebraicGeometry.Spec (.of P.field.k)) :
    AlgebraicGeometry.HasInvertibleExponent P.Coefficient T := by
  classical
  let l := P.coefficients.l
  let E := P.extension
  have hdvr := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (hdvr.2.1 _).2
    change spectralNorm (Padic l) E (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E),
      spectralNorm_extends (K := Padic l) (L := E)]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hkill : ((l ^ P.level : ℕ) : P.Coefficient) = 0 := by
    apply ULift.ext
    change ((l ^ P.level : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E P.level) = 0
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    rw [Nat.cast_pow]
    change (l : Padic.coefficientExtensionIntegers l E) ^ P.level ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ P.level
    rw [hgen]
    exact Ideal.pow_mem_pow hm P.level
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  have : CharP P.field.k P.field.p := charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hl : (l : P.field.k) ≠ 0 := by
    intro hz
    have hdiv := (CharP.cast_eq_zero_iff P.field.k P.field.p l).mp hz
    exact P.coefficients.different
      ((Nat.prime_dvd_prime_iff_eq P.field.prime (Fact.out : l.Prime)).mp hdiv).symm
  refine ⟨l ^ P.level, pow_pos (Nat.Prime.pos Fact.out) _, hkill, ?_⟩
  have hu := ((Ne.isUnit hl).pow P.level).map
    ((AlgebraicGeometry.Scheme.ΓSpecIso (.of P.field.k)).inv.hom)
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hu.map a.appTop.hom

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
