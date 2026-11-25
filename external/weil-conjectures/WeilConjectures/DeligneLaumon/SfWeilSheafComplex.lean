/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

import Mathlib.Algebra.CharP.CharAndCard

/-! # Weil complexes as fixed pairs on the recorded constructible categories

Source: Weil blueprint, order 1507, Weil sheaves and Weil complexes
(blueprint: definition-weil-structure).
These are fixed pairs in the constructible derived category, with its underlying Hom sets.
The derived category of Weil sheaves is a different construction.

## Main definitions

- `sfWeilComplex` and `sfCommonStageWeilComplex`: fixed-pair categories.
- `sfWeilSheaf` and `sfCommonStageWeilSheaf`: their full heart-carrier subcategories.
- `sfWeilStageObject`: the canonical finite-stage fixed-pair object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀)))
  [hft : LocallyOfFiniteType Y₀.hom] [hqc : QuasiCompact Y₀.hom]

include hl

/-- The coefficient prime is invertible on the actual geometric fibre.
Source: blueprint orders 1507 and 411 (blueprint: definition-weil-structure).
Proof: the residue fields of the base change are extensions of the chosen algebraic
closure of k₀, which has characteristic D.p by the specified finite cardinality.
The distinct prime l is nonzero in each residue field, hence invertible there. -/
theorem FiniteFieldDatum.geometricFiber_coefficientPrimeInvertible :
    ∀ x : (D.geometricFiber Y₀).left,
      IsUnit (l : (D.geometricFiber Y₀).left.residueField x) := by
  classical
  intro x
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
  let f := (D.geometricFiber Y₀).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  simpa only [map_natCast] using hunit.map
    ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ f.appTop ≫
      (D.geometricFiber Y₀).left.Γevaluation x).hom

/-- The inherited prime-invertibility structure; it imposes no additional hypothesis.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
@[instance_reducible]
def sfWeilPrimeInvertible (x : (D.geometricFiber Y₀).left) :
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
  (D.geometricFiber_coefficientPrimeInvertible l hl Y₀ x).invertible

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Frobenius pullback on the current rationalized constructible category.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
def sfWeilFrobeniusPullback :
    sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
      sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (D.geometricFrobenius Y₀).asIso.hom
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)

/-- E-Weil complexes are pairs (K,theta:Lg*K≅K); arrows are the commuting underlying
arrows, with their original identities and composition. IsoAlgebra is precisely the
recorded fixed-pair construction, including its faithful forgetful functor.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
abbrev sfWeilComplex := IsoAlgebra (sfWeilFrobeniusPullback D l hl Y₀ E)

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Frobenius pullback acts at each literal finite stage and on common-stage representatives.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
def sfCommonStageWeilFrobeniusPullback :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (D.geometricFrobenius Y₀).asIso.hom
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)

/-- Algebraically closed Weil complexes are fixed pairs in the actual common-stage category.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
abbrev sfCommonStageWeilComplex :=
  IsoAlgebra (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)

/-- The source equality for the actual common-stage pullback, as its defining object formula.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
def sfWeilStagePullbackIdentification (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Y₀).left L) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj K) :=
  eqToIso ((@commonStageDerivedPullback_existsUnique l _ Ω _ _ _ _ _
    (D.geometricFrobenius Y₀).asIso.hom
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)).exists.choose_spec.1 _)

/-- A finite-stage Weil pair maps to ((E,K),[E,theta]), with the inverse represented
by theta inverse. The stage-inclusion functor includes the self-transition associators.
Source: blueprint order 1507 (blueprint: definition-weil-structure). -/
def sfWeilStageObject (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) :
    sfCommonStageWeilComplex D l hl Y₀ Ω :=
  IsoAlgebra.mk ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K.carrier)
    (sfWeilStagePullbackIdentification D l hl Y₀ Ω L K.carrier ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).mapIso K.str)

end WeilConjectures
