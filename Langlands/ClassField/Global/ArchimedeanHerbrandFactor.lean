import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.GroupTheory.GroupAction.Basic

/-! # The archimedean factor in the cyclic Herbrand calculation -/

noncomputable section

open NumberField
open scoped BigOperators

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] [NumberField F]
variable (E : Type v) [Field E] [NumberField E] [Algebra F E]

/-- Galois-automorphism orbits of infinite places, without a Galois hypothesis. -/
abbrev infinitePlaceOrbits :=
  Quotient (MulAction.orbitRel (E ≃ₐ[F] E) (InfinitePlace E))

/-- The stabilizer order attached to an orbit of infinite places. -/
def infiniteOrbitStabilizerOrder : infinitePlaceOrbits F E → ℕ :=
  Quotient.lift (fun w => Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w))
    (fun _ _ h => Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv)

omit [NumberField F] [NumberField E] in
@[simp] theorem infiniteOrbitStabilizerOrder_mk (w : InfinitePlace E) :
    infiniteOrbitStabilizerOrder F E (Quotient.mk'' w) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w) := rfl

/-- Product of the stabilizer orders, with one factor for each infinite-place orbit. -/
def archimedeanHerbrandFactor : ℕ :=
  letI := Fintype.ofFinite (infinitePlaceOrbits F E)
  ∏ q : infinitePlaceOrbits F E, infiniteOrbitStabilizerOrder F E q

theorem infiniteOrbitStabilizerOrder_pos (q : infinitePlaceOrbits F E) :
    0 < infiniteOrbitStabilizerOrder F E q := by
  induction q using Quotient.inductionOn with
  | h w =>
    change 0 < Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w)
    exact Nat.card_pos

theorem archimedeanHerbrandFactor_pos : 0 < archimedeanHerbrandFactor F E := by
  classical
  let := Fintype.ofFinite (infinitePlaceOrbits F E)
  exact Finset.prod_pos (fun q _ => infiniteOrbitStabilizerOrder_pos F E q)

omit [NumberField F] in
/-- Any choice of representatives gives the same product. -/
theorem archimedeanHerbrandFactor_eq_prod
    (r : infinitePlaceOrbits F E → InfinitePlace E)
    (hr : ∀ q, (Quotient.mk'' (r q) : infinitePlaceOrbits F E) = q) :
    archimedeanHerbrandFactor F E =
      letI := Fintype.ofFinite (infinitePlaceOrbits F E)
      ∏ q : infinitePlaceOrbits F E, Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) (r q)) := by
  classical
  let := Fintype.ofFinite (infinitePlaceOrbits F E)
  apply Finset.prod_congr rfl
  intro q _
  rw [← hr q, infiniteOrbitStabilizerOrder_mk]
  rw [hr q]

@[simp] theorem archimedeanHerbrandFactor_self :
    archimedeanHerbrandFactor E E = 1 := by
  classical
  unfold archimedeanHerbrandFactor
  apply Finset.prod_eq_one
  intro q _
  induction q using Quotient.inductionOn with
  | h w =>
    change Nat.card (MulAction.stabilizer (E ≃ₐ[E] E) w) = 1
    exact Nat.card_unique

end Langlands.ClassField.Global
