/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientTwistAnnihilator
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Data.Nat.Prime.Infinite

/-! # Intrinsic coefficient twists without an auxiliary finite field

This file defines the Tate twists of the condensed coefficient rings, without finite-field
parameters on the completed line and its field images.

The primary coefficient interface uses continuous-function condensed rings for
O_E and E and the discrete finite quotient ring at exponent n+1. Finite lines use
the internal free-module functor on roots, equivalently their balanced tensor
with A_E,n+1 over Z/l^(n+1), since the quotient is annihilated by l^(n+1).
The integral transitions reduce coefficients and take l-th powers of roots.
The limit is taken in O_E,S-modules, so its scalar action is coordinatewise.
Signed powers use the internal Hom into the coefficient unit at negative degrees.
Tensoring their degree-zero objects uses the actual unbounded derived tensor.
For Qbar, the publicly imported upstream tateTwist and tateTwistFunctor are used.

## Main definitions
* `AlgebraicGeometry.ProEtale.coefficientFiniteTwistOne`
* `AlgebraicGeometry.ProEtale.coefficientIntegralTwistOne`
* `AlgebraicGeometry.ProEtale.coefficientRationalTwistOne`
* `AlgebraicGeometry.ProEtale.coefficientSignedTwist`
* `AlgebraicGeometry.ProEtale.coefficientTwistFunctor`
* `sfIntegralTwistingObject`
* `sfIntegralTwistingFunctor`
* `sfRationalTwistingFunctor`
* `sfQbarTwistingFunctor`
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

/-- Postcomposition by a continuous ring homomorphism, in the coefficient universe. -/
def twistContinuousRingMap {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousCoefficientRingSheaf B :=
  ⟨{ app := fun T ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((f.compLeftContinuous T.unop hf).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same continuous coefficient map on abelian ring objects. -/
abbrev twistContinuousMap {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (twistContinuousRingMap f hf)

/-- A continuous ring map preserves the pulled-back ring operations. -/
instance twistContinuousMap_isMonHom {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : IsMonHom (twistContinuousMap f hf) := by
  dsimp only [twistContinuousMap]
  infer_instance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- The continuous-function condensed integer coefficient ring. -/
abbrev twistIntegralRing : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)

/-- The continuous-function condensed rational coefficient ring. -/
abbrev twistRationalRing : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.continuousCoefficientRingObj E

/-- The discrete condensed finite quotient at positive exponent n+1. -/
abbrev twistFiniteRing (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionRing l E (n + 1))

/-- The quotient is continuous because uniformizer cosets are neighbourhoods. -/
theorem twistReduction_continuous (n : ℕ) :
    letI := spectralNorm.normedField ℚ_[l] E
    letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
    Continuous (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  let := spectralNorm.normedField ℚ_[l] E
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact (Padic.coefficientExtension_integers_coset_basis l E x).mem_of_mem
    (i := n) trivial

/-- The actual quotient coefficient map on condensed rings. -/
def twistReduction (n : ℕ) : twistIntegralRing l E ⟶ twistFiniteRing l E n :=
  letI := spectralNorm.normedField ℚ_[l] E
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  twistContinuousMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (twistReduction_continuous l E n)

/-- The specified coefficient morphism preserves the ring structure. -/
instance twistReduction_isMonHom (n : ℕ) : IsMonHom (twistReduction l E n) := by
  unfold twistReduction
  infer_instance

/-- The actual consecutive finite coefficient reduction. -/
def twistFiniteReduction (n : ℕ) : twistFiniteRing l E (n + 1) ⟶ twistFiniteRing l E n :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 2)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 2)) := ⟨rfl⟩
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  twistContinuousMap (Padic.coefficientExtensionTransition l E (n + 1))
    continuous_of_discreteTopology

/-- The specified coefficient morphism preserves the ring structure. -/
instance twistFiniteReduction_isMonHom (n : ℕ) : IsMonHom (twistFiniteReduction l E n) := by
  unfold twistFiniteReduction
  infer_instance

/-- Inclusion of continuous integral coefficients into continuous field coefficients. -/
def twistIntegralToRational : twistIntegralRing l E ⟶ twistRationalRing l E :=
  letI := spectralNorm.normedField ℚ_[l] E
  twistContinuousMap (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val

/-- The specified coefficient morphism preserves the ring structure. -/
instance twistIntegralToRational_isMonHom : IsMonHom (twistIntegralToRational l E) := by
  unfold twistIntegralToRational
  infer_instance

variable (X : Scheme.{u})

/-- The root presentation at exponent r+1 of the positive quotient A_E,n+1.
When l^(r+1) annihilates the quotient this is its tensor over (Z/l^(r+1))_X. -/
def coefficientFiniteRootLine (n r : ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing l E n) X) :=
  (Mod.freeFunctor _).obj (rootsOfUnitySheaf X (l ^ (r + 1)))

/-- The canonical comparison sends u tensor a to u^(l^k) tensor a. -/
def coefficientFiniteRootComparison (n r k : ℕ) :
    coefficientFiniteRootLine l E X n (r + k) ⟶ coefficientFiniteRootLine l E X n r :=
  (Mod.freeFunctor _).map
    (eqToHom (by rw [← pow_add]; congr 2; omega :
      rootsOfUnitySheaf X (l ^ (r + k + 1)) =
        rootsOfUnitySheaf X (l ^ k * l ^ (r + 1))) ≫
      rootsOfUnitySheafPow X (l ^ (r + 1)) (l ^ k))

/-- A_E,n+1(1) with the fixed exponent n+1 and its actual quotient coefficient action. -/
abbrev coefficientFiniteTwistOne (n : ℕ) := coefficientFiniteRootLine l E X n n

/-- Read the same finite line as an integral module through the quotient map. -/
def coefficientIntegralTwistLevel (n : ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistIntegralRing l E) X) :=
  (Mod.comap (coefficientMap (twistReduction l E n) X)).obj
    (coefficientFiniteTwistOne l E X n)

/-- The reduction coefficient square commutes before and after pullback. -/
theorem twistReduction_comp (n : ℕ) :
    coefficientMap (twistReduction l E (n + 1)) X ≫
      coefficientMap (twistFiniteReduction l E n) X =
        coefficientMap (twistReduction l E n) X := by
  rw [← coefficientMap_comp]
  apply congrArg (fun f ↦ coefficientMap f X)
  ext T a
  rfl

/-- Consecutive Tate levels: reduce coefficients and raise the root to its l-th power. -/
def coefficientIntegralTwistTransition (n : ℕ) :
    coefficientIntegralTwistLevel l E X (n + 1) ⟶ coefficientIntegralTwistLevel l E X n :=
  (coefficientFreeTensor_linear
    (coefficientMap (twistReduction l E (n + 1)) X)
    (coefficientMap (twistReduction l E n) X)
    (coefficientMap (twistFiniteReduction l E n) X) (twistReduction_comp l E X n)
    (eqToHom (by rw [pow_succ'] :
      rootsOfUnitySheaf X (l ^ (n + 2)) = rootsOfUnitySheaf X (l * l ^ (n + 1))) ≫
        rootsOfUnitySheafPow X (l ^ (n + 1)) l)).exists.choose

/-- The positive finite Tate tower, in integral coefficient modules. -/
def coefficientIntegralTwistSystem :
    ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistIntegralRing l E) X) :=
  Functor.ofOpSequence (coefficientIntegralTwistTransition l E X)

/-- O_E,X(1), constructed as the actual inverse limit of the finite root lines. -/
def coefficientIntegralTwistOne :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistIntegralRing l E) X) :=
  limit (coefficientIntegralTwistSystem l E X)

/-- E_X(1), the balanced scalar extension of the integral limit line. -/
def coefficientRationalTwistOne :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistRationalRing l E) X) :=
  (Mod.extendScalars (coefficientMap (twistIntegralToRational l E) X)).obj
    (coefficientIntegralTwistOne l E X)

/-- Nonnegative powers of a coefficient line, with degree zero the coefficient unit. -/
def coefficientTwistNat (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    ℕ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  | 0 => 𝟙_ _
  | n + 1 => coefficientTwistNat R L n ⊗ L

/-- Negative powers are the internal sheaf Hom of the positive power into the unit. -/
def coefficientSignedTwist (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    ℤ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  | (n : ℕ) => coefficientTwistNat X R L n
  | .negSucc n => (ihom (coefficientTwistNat X R L (n + 1))).obj (𝟙_ _)

/-- K(m) is derived tensor with the signed line placed in degree zero. -/
def coefficientTwistFunctor (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (m : ℤ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
  tensorRight ((DerivedCategory.singleFunctor _ 0).obj (coefficientSignedTwist X R L m))

/-- The finite twist functor on the unbounded finite-coefficient derived category. -/
abbrev coefficientFiniteTwistFunctor (n : ℕ) (m : ℤ) :=
  coefficientTwistFunctor X _ (coefficientFiniteTwistOne l E X n) m

/-- The integral twist functor on the unbounded continuous-coefficient derived category. -/
abbrev coefficientIntegralTwistFunctor (m : ℤ) :=
  coefficientTwistFunctor X _ (coefficientIntegralTwistOne l E X) m

/-- The rational twist functor on the unbounded continuous-coefficient derived category. -/
abbrev coefficientRationalTwistFunctor (m : ℤ) :=
  coefficientTwistFunctor X _ (coefficientRationalTwistOne l E X) m

end AlgebraicGeometry.ProEtale

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- The completed signed line in degree zero, with no finite-field datum. -/
abbrev sfIntegralTwistingObject (m : ℤ) : DerivedCategory (scalarReductionSource l E S) :=
  (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E S m)

/-- Intrinsic membership of the completed signed line. -/
theorem sfIntegralTwistingObject_mem (m : ℤ) :
    sfIntegralConstructible l E S (sfIntegralTwistingObject l E S m) := by
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  exact intrinsicIntegralCoefficientTwist_mem D l hl E S m

/-- The same signed line as an object of the recorded intrinsic full subcategory. -/
def sfIntegralTwistingCoefficient (m : ℤ) : sfIntegralConstructibleCategory l E S :=
  ⟨sfIntegralTwistingObject l E S m, sfIntegralTwistingObject_mem l E S m⟩

/-- The recorded exact tensor on completed module sheaves, descended termwise. -/
abbrev sfIntegralTwistingFunctor (m : ℤ) :=
  (integralSheafTwist l E S m).mapDerivedCategory

/-- The image of the signed integral line under the recorded raw rationalization. -/
def sfRationalTwistingCoefficient (m : ℤ) : sfRationalConstructibleCategory l E S :=
  (sfRationalConstructibleLocalization l E S).obj (sfIntegralTwistingCoefficient l E S m)

/-- Tensor by that image, using the unique bilinear intrinsic rational tensor.
Objects are the integral tensor representatives; localized arrows are sent by
(a tensor f, b tensor g) to ab tensor (f tensor g), as specified by rationalDerivedTensor. -/
def sfRationalTwistingFunctor (m : ℤ) :
    sfRationalConstructibleCategory l E S ⥤ sfRationalConstructibleCategory l E S :=
  (𝟭 (sfRationalConstructibleCategory l E S)).prod'
    ((Functor.const (sfRationalConstructibleCategory l E S)).obj
      (sfRationalTwistingCoefficient l E S m)) ⋙ rationalDerivedTensor l E S

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The same line represented at the least finite coefficient stage. -/
def sfQbarTwistingCoefficient (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω S :=
  ⟨Padic.finiteCoefficientBase l Ω,
    sfRationalTwistingCoefficient l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) S m⟩

/-- The recorded common-stage tensor with the same signed line. Its arrows and
scalar comparisons are exactly those of commonStageDerivedTensor. -/
def sfQbarTwistingFunctor (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω S ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω S :=
  (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω S)).prod'
    ((Functor.const (generalAlgebraicallyClosedConstructibleCategory l Ω S)).obj
      (sfQbarTwistingCoefficient l S Ω m)) ⋙ commonStageDerivedTensor l Ω S

end WeilConjectures
