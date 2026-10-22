import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Instances.AddCircle.Defs

/-! # Actual multiplicative Galois coefficient modules and cohomology

The scalar ring is an explicit universe lift of the integers. The field,
automorphism group and unit group are unchanged.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- Integers in the universe used by Mathlib's finite group cohomology API. -/
abbrev IntegerScalars := ULift.{u} ℤ

/-- The scalar lift is the actual integer ring, via the explicit down equivalence. -/
def integerScalarsEquiv : IntegerScalars.{u} ≃+* ℤ := ULift.ringEquiv

/-- The actual Galois action on the additive notation for the field's unit group. -/
def unitsRepresentation (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] :
    Rep.{u} IntegerScalars.{u} Gal(L/K) :=
  Rep.of
    { toFun σ := ((Rep.ofAlgebraAutOnUnits K L).ρ σ).restrictScalars IntegerScalars.{u}
      map_one' := by
        ext x
        exact LinearMap.congr_fun (map_one (Rep.ofAlgebraAutOnUnits K L).ρ) x
      map_mul' σ τ := by
        ext x
        exact LinearMap.congr_fun (map_mul (Rep.ofAlgebraAutOnUnits K L).ρ σ τ) x }

/-- The unit module with its discrete topology and actual automorphism action. -/
def discreteUnitsRepresentation (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] :
    TopRep.{u} IntegerScalars.{u} Gal(L/K) := by
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  letI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  exact TopRep.of (X := Additive Lˣ) <| ContRepresentation.ofMonoidHom
    { toFun σ :=
        { toLinearMap := ((unitsRepresentation K L).ρ σ :
            Additive Lˣ →ₗ[IntegerScalars.{u}] Additive Lˣ)
          cont := continuous_of_discreteTopology }
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (map_one (unitsRepresentation K L).ρ) x
      map_mul' σ τ := by
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (map_mul (unitsRepresentation K L).ρ σ τ) x }

instance (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L] :
    DiscreteTopology (discreteUnitsRepresentation K L) := ⟨rfl⟩

/-- The stabilizer of a unit is open, with the Krull-topology certificate. -/
def unitOpenStabilizer (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] (x : Lˣ) :
    OpenSubgroup Gal(L/K) where
  toSubgroup := (MulAction.stabilizer Gal(L/K) (x : L))
  isOpen' := stabilizer_isOpen_of_isIntegral (K := K) (x : L)

/-- This open subgroup is precisely the stabilizer for the unit representation. -/
theorem mem_unitOpenStabilizer_iff (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (x : Additive Lˣ) (σ : Gal(L/K)) :
    σ ∈ unitOpenStabilizer K L x.toMul ↔
      (discreteUnitsRepresentation K L).ρ σ x = x := by
  change σ (x.toMul : L) = (x.toMul : L) ↔ _
  constructor
  · intro h
    apply Units.ext
    exact h
  · intro h
    exact congrArg (fun y : Additive Lˣ => (y.toMul : L)) h

/-- The actual algebraic-closure unit module for the absolute Galois group. -/
abbrev absoluteUnits (K : Type u) [Field K] :
    TopRep.{u} IntegerScalars.{u} (Field.absoluteGaloisGroup K) :=
  discreteUnitsRepresentation K (AlgebraicClosure K)

/-- Continuous absolute Galois cohomology of the discrete algebraic-closure units. -/
abbrev absoluteCohomology (K : Type u) [Field K] (n : ℕ) :
    TopModuleCat.{u} IntegerScalars.{u} :=
  continuousCohomology n (absoluteUnits K)

/-- Ordinary relative cohomology, computed by Mathlib's inhomogeneous complex. -/
abbrev relativeCohomology (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] (n : ℕ) :
    ModuleCat.{u} IntegerScalars.{u} :=
  groupCohomology (unitsRepresentation K L) n

/-- Tate cohomology for the actual finite automorphism group and unit action. -/
abbrev relativeTateCohomology (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℤ) :
    ModuleCat.{u} IntegerScalars.{u} :=
  letI := Fintype.ofFinite Gal(L/K)
  tateCohomology (unitsRepresentation K L) n

/-- Tate cohomology of the trivial integral coefficient module. -/
abbrev integralTateCohomology (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℤ) :
    ModuleCat.{u} IntegerScalars.{u} :=
  letI := Fintype.ofFinite Gal(L/K)
  tateCohomology (Rep.trivial IntegerScalars.{u} Gal(L/K) IntegerScalars.{u}) n

/-- The actual quotient of the additive rationals by the subgroup of integers. -/
abbrev RationalModIntegers := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- The class of a rational number modulo the integers. -/
def rationalClass : ℚ →+ RationalModIntegers :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))

/-- The subgroup `(1/n)ℤ/ℤ`, characterized intrinsically by annihilation by `n`. -/
def denominatorSubgroup (n : ℕ) : AddSubgroup RationalModIntegers where
  carrier := {x | n • x = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all
  neg_mem' := by intro x hx; simp_all

/-- The positive, arithmetic-Frobenius convention for the invariant `1/n`. -/
def reciprocalClass (n : ℕ) : RationalModIntegers :=
  rationalClass ((n : ℚ)⁻¹)

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The coefficient morphism for base-field restriction is the identity on `Mˣ`. -/
def restrictionCoefficients :
    Rep.res (AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K))
      (unitsRepresentation K M) ⟶ unitsRepresentation L M :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }

/-- Genuine restriction induced by `Gal(M/L) → Gal(M/K)` on cochains. -/
abbrev relativeRestriction (n : ℕ) :
    relativeCohomology K M n ⟶ relativeCohomology L M n :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (restrictionCoefficients K L M) n

/-- Inclusion of the actual unit groups as a homomorphism of additive groups. -/
def unitInclusion : Additive Lˣ →+ Additive Mˣ :=
  (Units.map (algebraMap L M).toMonoidHom).toAdditive

/-- The same inclusion is linear over the explicitly lifted integers. -/
def unitInclusionLinear : Additive Lˣ →ₗ[IntegerScalars.{u}] Additive Mˣ :=
  (unitInclusion L M).toIntLinearMap.restrictScalars IntegerScalars.{u}

variable [Normal K L]

/-- The coefficient inclusion compatible with normal restriction of automorphisms. -/
def inflationCoefficients :
    Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K))
      (unitsRepresentation K L) ⟶ unitsRepresentation K M :=
  Rep.ofHom
    { toLinearMap := unitInclusionLinear L M
      isIntertwining' σ := by
        ext x
        apply Units.ext
        exact (AlgEquiv.restrictNormal_commutes σ L x.val) }

/-- Genuine inflation, using normal restriction and the coefficient inclusion. -/
abbrev relativeInflation (n : ℕ) :
    relativeCohomology K L n ⟶ relativeCohomology K M n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom L)
    (inflationCoefficients K L M) n

end Tower

section AbsoluteRestriction

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- Unit inclusion for specified compatible algebraic closures, with equivariance. -/
def absoluteRestrictionCoefficients :
    TopRep.res (Field.absoluteGaloisGroup.mapOfAlgebra K L)
      (absoluteUnits K) ⟶ absoluteUnits L where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear (AlgebraicClosure K) (AlgebraicClosure L)
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K)
          (AlgebraicClosure K) x.val }

/-- Actual continuous absolute restriction, for a specified closure embedding. -/
abbrev absoluteRestriction (n : ℕ) :
    absoluteCohomology K n ⟶ absoluteCohomology L n :=
  ContinuousCohomology.map (Field.absoluteGaloisGroup.mapOfAlgebra K L)
    (absoluteRestrictionCoefficients K L) n

end AbsoluteRestriction

end Langlands.ClassFieldTheory.Local
