import Langlands.Global.Arithmetic.GeneralPositionStatement

/-! # The local cyclic prime-step tower used in Harris's general position -/

namespace Langlands.Global

universe u

open LocalFactor.CommonClosure GeneralPosition

/-- Every finite Galois extension of a p-adic field in the common closure
admits a descending tower to the base field with the existing cyclic
prime-step convention. This isolates the field-theoretic part of Harris 1998,
Definition 4.5(i), using local Galois solvability (Serre IV.2, Corollary 5).
It is a proposition target, not a proof of general position. -/
def HarrisCyclicPrimeTowerStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : Extension F) [IsGalois F.Carrier E.field],
    ∃ (n : ℕ) (T : Fin (n + 1) → Extension F),
      (T 0).field = E.field ∧ (T (Fin.last n)).field = ⊥ ∧
        ∀ i : Fin n, IsCyclicPrimeStep F (T i.succ) (T i.castSucc)

end Langlands.Global
