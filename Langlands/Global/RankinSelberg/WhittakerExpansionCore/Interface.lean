import Langlands.Global.RankinSelberg.ProjectionExpansion
import Langlands.Automorphic.GeneralLinearCuspidalComparison
import Langlands.Automorphic.CuspidalL2.UnipotentMeanValue

/-! # Interface of the analytic core of the Whittaker expansion

The definitions shared by the two halves of the proof:

* (S) every function of a `WhittakerDecayClass` has locally uniform summable majorants for its
  Whittaker terms at every level (`HasWhittakerMajorants`, `WhittakerMajorantsStatement`);
* (E) a continuous, left `GL_{r+1}(F)`-invariant cuspidal function whose Whittaker terms are
  summable at every level is the sum of its Whittaker expansion (module `ExpansionInduction`). -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

local instance interfaceSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The Whittaker function `W_f` with all simple-root coefficients `1`. -/
abbrev whittaker (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ) :
    Points F (r + 1) → ℂ :=
  generalLinearWhittakerFunction F r ψ (fun _ => 1) f

/-- Locally uniform summable majorants of the Whittaker terms at every level `j ≤ r`: for every
compact `C` there is a summable `b` on `N_j(F) \ GL_j(F)` with
`‖W_f(diag(γ_q, I) x)‖ ≤ b q` for all `x ∈ C`. -/
def HasWhittakerMajorants (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ) :
    Prop :=
  ∀ (j : ℕ) (hj : j ≤ r) (C : Set (Points F (r + 1))), IsCompact C →
    ∃ b : UnipotentRationalCosets F j → ℝ, Summable b ∧
      ∀ (q : UnipotentRationalCosets F j) (x : Points F (r + 1)), x ∈ C →
        ‖whittaker F r ψ f (padRational F (Nat.le_succ_of_le hj) q.out * x)‖ ≤ b q

/-- The adelic point with archimedean component `1 + Z` (for `Z * Z = 0`) and finite
component `1`. -/
def archPoint (n : ℕ) (Z : ArchimedeanMatrix F n) (hZ : Z * Z = 0) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (AdelicGL.ofInfinite F n (ArchimedeanGL.squareZeroElement Z hZ))

/-- The adelic point of a finite adelic matrix. -/
def finitePoint (n : ℕ) (l : FiniteAdelicGL F n) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofFinite F n l)

/-- A space `V` of functions on `GL_{r+1}(𝔸)` with a real-linear family `R` of archimedean
right derivatives, to which the decay argument applies: continuity, left invariance under
rational points, finite level, boundedness on every band `lo ≤ |det| ≤ hi`, and
`d/dt f(x (1 + t Z)) = (R Z f)(x)` at `t = 0` for square-zero `Z`. -/
structure WhittakerDecayClass (r : ℕ) (V : Submodule ℂ (Points F (r + 1) → ℂ))
    (R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V) : Prop where
  continuous : ∀ f : V, Continuous (f : Points F (r + 1) → ℂ)
  rational : ∀ (f : V) (y : Points F (r + 1)),
    y ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)) →
      ∀ x, (f : Points F (r + 1) → ℂ) (y * x) = (f : Points F (r + 1) → ℂ) x
  level : ∀ f : V, ∃ L : Subgroup (FiniteAdelicGL F (r + 1)),
    IsOpen (L : Set (FiniteAdelicGL F (r + 1))) ∧
      ∀ x, ∀ l ∈ L, (f : Points F (r + 1) → ℂ) (x * finitePoint F (r + 1) l) =
        (f : Points F (r + 1) → ℂ) x
  bounded : ∀ (f : V) (lo hi : ℝ), 0 < lo → ∃ B : ℝ, ∀ x : Points F (r + 1),
    lo ≤ detNorm F (r + 1) x → detNorm F (r + 1) x ≤ hi → ‖(f : Points F (r + 1) → ℂ) x‖ ≤ B
  deriv : ∀ (f : V) (Z : ArchimedeanMatrix F (r + 1)) (hZ : Z * Z = 0) (x : Points F (r + 1)),
    HasDerivAt (fun t : ℝ => (f : Points F (r + 1) → ℂ)
        (x * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      (((R Z f : V) : Points F (r + 1) → ℂ) x) 0

variable [CompactSpace (AdeleQuotient F)]

/-- Half (S): every function of a decay class has locally uniform majorants. -/
def WhittakerMajorantsStatement : Prop :=
  ∀ (r : ℕ) (V : Submodule ℂ (Points F (r + 1) → ℂ))
    (R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V), WhittakerDecayClass F r V R →
    ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ f : V, HasWhittakerMajorants F r ψ f

end Langlands.Global.RankinSelbergGlobal.Unfolding
