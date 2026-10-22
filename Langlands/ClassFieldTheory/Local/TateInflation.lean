import Langlands.ClassFieldTheory.Local.TateCup

/-! # Inflation in positive Tate degrees -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

section Comparison

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]

/-- Ordinary cohomology of the actual trivial integral representation. -/
abbrev integralCohomology (n : ℕ) : ModuleCat.{u} IntegerScalars.{u} :=
  groupCohomology (Rep.trivial IntegerScalars.{u} Gal(L/K) IntegerScalars.{u}) n

variable [FiniteDimensional K L]

/-- Positive relative Tate cohomology agrees with actual ordinary cohomology. -/
def relativeTateToOrdinary (n : ℕ) [NeZero n] :
    relativeTateCohomology K L n ≃ₗ[IntegerScalars.{u}] relativeCohomology K L n := by
  letI := Fintype.ofFinite Gal(L/K)
  exact ((TateCohomology.isoGroupCohomology n).app
    (unitsRepresentation K L)).toLinearEquiv

/-- The positive comparison for the actual trivial integral representation. -/
def integralTateToOrdinary (n : ℕ) [NeZero n] :
    integralTateCohomology K L n ≃ₗ[IntegerScalars.{u}] integralCohomology K L n := by
  letI := Fintype.ofFinite Gal(L/K)
  exact ((TateCohomology.isoGroupCohomology n).app
    (Rep.trivial IntegerScalars.{u} Gal(L/K) IntegerScalars.{u})).toLinearEquiv

end Comparison

section Tower

variable (K : Type v) (L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L]

/-- Ordinary inflation on units, allowing the base field an independent universe.
The coefficient map is actual unit inclusion. -/
def relativeInflationLinear (n : ℕ) :
    relativeCohomology K L n →ₗ[IntegerScalars.{u}] relativeCohomology K M n :=
  (groupCohomology.map (AlgEquiv.restrictNormalHom L)
    (Rep.ofHom
      { toLinearMap :=
          (Units.map (algebraMap L M).toMonoidHom).toAdditive.toIntLinearMap.restrictScalars
            IntegerScalars.{u}
        isIntertwining' σ := by
          ext x
          apply Units.ext
          exact AlgEquiv.restrictNormal_commutes σ L x.val }) n).hom

/-- Ordinary integral inflation uses normal restriction and identity coefficients. -/
def integralInflation (n : ℕ) :
    integralCohomology K L n →ₗ[IntegerScalars.{u}] integralCohomology K M n :=
  (groupCohomology.map (AlgEquiv.restrictNormalHom L)
    (Rep.ofHom
      { toLinearMap := LinearMap.id
        isIntertwining' _ := rfl }) n).hom

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- Positive Tate inflation is the transport of actual ordinary unit inflation. -/
def relativePositiveTateInflation (n : ℕ) [NeZero n] :
    relativeTateCohomology K L n →ₗ[IntegerScalars.{u}]
      relativeTateCohomology K M n :=
  (relativeTateToOrdinary K M n).symm.toLinearMap.comp
    ((relativeInflationLinear K L M n).comp
      (relativeTateToOrdinary K L n).toLinearMap)

/-- Positive Tate inflation on the trivial integral coefficients. -/
def integralPositiveTateInflation (n : ℕ) [NeZero n] :
    integralTateCohomology K L n →ₗ[IntegerScalars.{u}]
      integralTateCohomology K M n :=
  (integralTateToOrdinary K M n).symm.toLinearMap.comp
    ((integralInflation K L M n).comp
      (integralTateToOrdinary K L n).toLinearMap)

/-- The constructed unit map commutes with the positive comparison. -/
theorem relativePositiveTateInflation_comparison (n : ℕ) [NeZero n]
    (x : relativeTateCohomology K L n) :
    relativeTateToOrdinary K M n (relativePositiveTateInflation K L M n x) =
      relativeInflationLinear K L M n (relativeTateToOrdinary K L n x) :=
  (relativeTateToOrdinary K M n).apply_symm_apply _

/-- The constructed integral map commutes with the positive comparison. -/
theorem integralPositiveTateInflation_comparison (n : ℕ) [NeZero n]
    (x : integralTateCohomology K L n) :
    integralTateToOrdinary K M n (integralPositiveTateInflation K L M n x) =
      integralInflation K L M n (integralTateToOrdinary K L n x) :=
  (integralTateToOrdinary K M n).apply_symm_apply _

/-- Cup naturality under actual inflation, in positive degrees. -/
def PositiveTateCupInflation : Prop :=
  ∀ (n : ℕ) [NeZero n] (c : relativeCohomology K L 2)
    (x : integralTateCohomology K L n),
    relativePositiveTateInflation K L M (n + 2) (relativeTateCup K L n c x) =
      relativeTateCup K M n (relativeInflationLinear K L M 2 c)
        (integralPositiveTateInflation K L M n x)

/-- Fundamental-class cup commutes with inflation up to the upper extension
degree, in positive degrees. This predicate assumes no compatibility laws. -/
def FundamentalClassPositiveTateInflation
    (invKL : relativeCohomology K L 2 →+ RationalModIntegers)
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass K L invKL c → IsFundamentalClass K M invKM d →
    ∀ (n : ℕ) [NeZero n] (x : integralTateCohomology K L n),
      relativePositiveTateInflation K L M (n + 2) (relativeTateCup K L n c x) =
        Module.finrank L M •
          relativeTateCup K M n d (integralPositiveTateInflation K L M n x)

end Tower

section ExistingInflation

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L]

/-- In the common-universe setting, the generalized ordinary map is exactly
the existing relative inflation. -/
theorem relativeInflationLinear_eq (n : ℕ) :
    relativeInflationLinear K L M n = (relativeInflation K L M n).hom := rfl

end ExistingInflation

namespace InvariantFamily

/-- The positive-degree scaled inflation diagram for the same raw family,
over every finite Galois tower above a p-adic field. -/
def PositiveTateInflation {p : ℕ} [Fact p.Prime] (I : InvariantFamily.{v,u} p) :
    Prop :=
  ∀ (F : PadicField.{v} p) (L M : Type u)
    [Field L] [Field M] [Algebra F.Carrier L] [Algebra F.Carrier M]
    [Algebra L M] [IsScalarTower F.Carrier L M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier L] [IsGalois F.Carrier M],
    FundamentalClassPositiveTateInflation F.Carrier L M
      (I.relative F L) (I.relative F M)

end InvariantFamily

end Langlands.ClassFieldTheory.Local
