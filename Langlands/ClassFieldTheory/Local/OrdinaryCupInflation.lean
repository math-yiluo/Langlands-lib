import Langlands.ClassFieldTheory.Local.TateInflation
import Langlands.Cohomology.Tate.OrdinaryTateCupProof

/-! # Ordinary local cup products and inflation in nonnegative degrees -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

set_option backward.isDefEq.respectTransparency false

private theorem ordinaryToTate_degree {R G : Type u} [CommRing R] [Group G]
    [Fintype G] (A : Rep.{u} R G) {m n : ℕ} (h : m = n)
    (x : groupCohomology A m) :
    Langlands.Tate.ordinaryToTate A n
      ((eqToIso (congrArg (groupCohomology A) h)).hom x) =
      (Langlands.Tate.tateDegreeIso A
        (congrArg (fun k : ℕ => (k : ℤ)) h)).hom
        (Langlands.Tate.ordinaryToTate A m x) := by
  subst n
  rfl

private theorem tateDegreeIso_comp_apply {R G : Type u} [CommRing R] [Group G]
    [Fintype G] (A : Rep.{u} R G) {m n k : ℤ} (h : m = n) (h' : n = k)
    (x : tateCohomology A m) :
    (Langlands.Tate.tateDegreeIso A h').hom
      ((Langlands.Tate.tateDegreeIso A h).hom x) =
      (Langlands.Tate.tateDegreeIso A (h.trans h')).hom x := by
  subst n k
  rfl

section Extension

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]

/-- Ordinary cup with a relative degree-two class on the left and actual
trivial integral coefficients on the right. -/
def relativeOrdinaryCup (n : ℕ) (c : relativeCohomology K L 2) :
    integralCohomology K L n →ₗ[IntegerScalars.{u}]
      relativeCohomology K L (n + 2) :=
  ((eqToIso (congrArg (relativeCohomology K L) (Nat.add_comm 2 n))).hom).hom.comp
    (Langlands.Tate.ordinaryCup
      (Langlands.Tate.scalarPairing (unitsRepresentation K L)) 2 n c)

variable [FiniteDimensional K L]

/-- The actual ordinary-to-Tate comparison on relative unit cohomology,
including its norm-quotient map in degree zero. -/
def relativeOrdinaryToTate (n : ℕ) :
    relativeCohomology K L n →ₗ[IntegerScalars.{u}]
      relativeTateCohomology K L n := by
  letI := Fintype.ofFinite Gal(L/K)
  exact (Langlands.Tate.ordinaryToTate (unitsRepresentation K L) n).hom

/-- The actual comparison for the trivial lifted-integer representation. -/
def integralOrdinaryToTate (n : ℕ) :
    integralCohomology K L n →ₗ[IntegerScalars.{u}]
      integralTateCohomology K L n := by
  letI := Fintype.ofFinite Gal(L/K)
  exact (Langlands.Tate.ordinaryToTate
    (Rep.trivial IntegerScalars.{u} Gal(L/K) IntegerScalars.{u}) n).hom

/-- Cup comparison in every natural input degree. The output is transported
from the cast of the natural degree to the corresponding integer sum. -/
theorem relativeOrdinaryCup_comparison (n : ℕ) (c : relativeCohomology K L 2)
    (x : integralCohomology K L n) :
    letI := Fintype.ofFinite Gal(L/K)
    (Langlands.Tate.tateDegreeIso (unitsRepresentation K L)
      (show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega)).hom
      (relativeOrdinaryToTate K L (n + 2) (relativeOrdinaryCup K L n c x)) =
      relativeTateCup K L n c (integralOrdinaryToTate K L n x) := by
  let := Fintype.ofFinite Gal(L/K)
  change (Langlands.Tate.tateDegreeIso (unitsRepresentation K L)
    (show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega)).hom
    (Langlands.Tate.ordinaryToTate (unitsRepresentation K L) (n + 2)
      ((eqToIso (congrArg (groupCohomology (unitsRepresentation K L))
        (Nat.add_comm 2 n))).hom
        (Langlands.Tate.ordinaryCup
          (Langlands.Tate.scalarPairing (unitsRepresentation K L)) 2 n c x))) =
    (Langlands.Tate.tateDegreeIso (unitsRepresentation K L)
      (add_comm (2 : ℤ) (n : ℤ))).hom
      (Langlands.Tate.cup
        (Langlands.Tate.scalarPairing (unitsRepresentation K L)) 2 n
        (((TateCohomology.isoGroupCohomology 2).app
          (unitsRepresentation K L)).inv c)
        (Langlands.Tate.ordinaryToTate
          (Rep.trivial IntegerScalars.{u} Gal(L/K) IntegerScalars.{u}) n x))
  rw [ordinaryToTate_degree (unitsRepresentation K L) (Nat.add_comm 2 n),
    tateDegreeIso_comp_apply]
  have comparison := Langlands.Tate.ordinaryToTate_cup
    (Langlands.Tate.scalarPairing (unitsRepresentation K L)) 2 n c x
  have h := congrArg ((Langlands.Tate.tateDegreeIso (unitsRepresentation K L)
      (add_comm (2 : ℤ) (n : ℤ))).hom) comparison
  erw [tateDegreeIso_comp_apply (unitsRepresentation K L)
    (show ((2 + n : ℕ) : ℤ) = (2 : ℤ) + n by omega)
    (add_comm (2 : ℤ) (n : ℤ))] at h
  simp only [Langlands.Tate.ordinaryToTate_pos] at h ⊢
  convert h using 1

end Extension

section Tower

variable (K : Type v) (L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L]

/-- Ordinary cup naturality for actual unit and integral inflation,
including degree zero. -/
def OrdinaryCupInflation : Prop :=
  ∀ (n : ℕ) (c : relativeCohomology K L 2) (x : integralCohomology K L n),
    relativeInflationLinear K L M (n + 2) (relativeOrdinaryCup K L n c x) =
      relativeOrdinaryCup K M n (relativeInflationLinear K L M 2 c)
        (integralInflation K L M n x)

/-- The upper-extension-degree scaled ordinary inflation diagram, with
fundamental classes quantified without choice. -/
def FundamentalClassOrdinaryInflation
    (invKL : relativeCohomology K L 2 →+ RationalModIntegers)
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass K L invKL c → IsFundamentalClass K M invKM d →
    ∀ (n : ℕ) (x : integralCohomology K L n),
      relativeInflationLinear K L M (n + 2) (relativeOrdinaryCup K L n c x) =
        Module.finrank L M •
          relativeOrdinaryCup K M n d (integralInflation K L M n x)

end Tower

namespace InvariantFamily

/-- The degree-scaled ordinary cup inflation diagram for the same raw
invariant family, in every natural degree over every finite Galois tower. -/
def OrdinaryInflation {p : ℕ} [Fact p.Prime] (I : InvariantFamily.{v,u} p) :
    Prop :=
  ∀ (F : PadicField.{v} p) (L M : Type u)
    [Field L] [Field M] [Algebra F.Carrier L] [Algebra F.Carrier M]
    [Algebra L M] [IsScalarTower F.Carrier L M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier L] [IsGalois F.Carrier M],
    FundamentalClassOrdinaryInflation F.Carrier L M
      (I.relative F L) (I.relative F M)

end InvariantFamily

end Langlands.ClassFieldTheory.Local
