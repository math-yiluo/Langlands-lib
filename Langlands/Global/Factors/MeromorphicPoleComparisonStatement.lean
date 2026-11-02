import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Pole comparison after removing holomorphic nonzero factors

These are conditional statements about actual complex functions and punctured
germs. Boundary regularity is separate from regularity of the finitely many
omitted local factors.
-/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.Global.PoleComparison

universe u v

/-- A factor which is holomorphic and nonzero at the specified point. -/
def HolomorphicUnitAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  AnalyticAt ℂ f z ∧ f z ≠ 0

/-- The actual finite product of the omitted local factors. -/
def omittedProduct {A : Type u} (S : Finset A) (f : A → ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∏ a ∈ S, f a z

/-- The completed factor whose distinguished local factor is to be compared.
The boundary factor can include a partial global L-function or other tail. -/
def completedProduct {A : Type u} (S : Finset A) (localFactor : ℂ → ℂ)
    (omitted : A → ℂ → ℂ) (boundary : ℂ → ℂ) : ℂ → ℂ :=
  fun z => boundary z * (omittedProduct S omitted z * localFactor z)

/-- Local regularity of each factor removed from a finite product. -/
def OmittedUnitsAt {A : Type u} (S : Finset A) (f : A → ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ a ∈ S, HolomorphicUnitAt (f a) z

/-- Removing a finite family of holomorphic nonzero factors and a separately
specified holomorphic nonzero boundary factor preserves the distinguished order.
There is no nonzero value assumption on the distinguished factor. -/
def FiniteOmittedOrderStatement (A : Type u) : Prop :=
  ∀ (S : Finset A) (localFactor : ℂ → ℂ) (omitted : A → ℂ → ℂ)
    (boundary : ℂ → ℂ) (z : ℂ),
    OmittedUnitsAt S omitted z →
    HolomorphicUnitAt boundary z →
    meromorphicOrderAt (completedProduct S localFactor omitted boundary) z =
      meromorphicOrderAt localFactor z

/-- Equality of completed punctured germs transfers the order to the two
distinguished meromorphic local factors only after every omitted factor and
both boundary factors have been shown holomorphic and nonzero. -/
def CompletedPoleTransferStatement (A : Type u) (B : Type v) : Prop :=
  ∀ (S : Finset A) (T : Finset B) (left right : ℂ → ℂ)
    (leftOmitted : A → ℂ → ℂ) (rightOmitted : B → ℂ → ℂ)
    (leftBoundary rightBoundary : ℂ → ℂ) (z : ℂ),
    MeromorphicAt left z →
    MeromorphicAt right z →
    OmittedUnitsAt S leftOmitted z →
    OmittedUnitsAt T rightOmitted z →
    HolomorphicUnitAt leftBoundary z →
    HolomorphicUnitAt rightBoundary z →
    (completedProduct S left leftOmitted leftBoundary =ᶠ[𝓝[≠] z]
      completedProduct T right rightOmitted rightBoundary) →
    meromorphicOrderAt left z = meromorphicOrderAt right z

/-- The finite-product and punctured-germ pole-transfer engine. This proposition
does not supply any global functional equation or global nonvanishing theorem. -/
def MeromorphicPoleComparisonStatement (A : Type u) (B : Type v) : Prop :=
  FiniteOmittedOrderStatement A ∧
  FiniteOmittedOrderStatement B ∧
  CompletedPoleTransferStatement A B

end Langlands.Global.PoleComparison
