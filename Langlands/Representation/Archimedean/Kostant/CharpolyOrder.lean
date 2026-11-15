import Langlands.Representation.Archimedean.Kostant.Coordinates
import Langlands.Representation.Archimedean.Kostant.WeightLex
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# A monomial order adapted to the characteristic polynomials of generic blocks

The variables `X ⟨b, p, q⟩` of `ℂ[X_c]`, `c ∈ Coord n`, get the weight `q` (the column
index). Ties are broken by the lexicographic order of `Coord n →₀ ℕ` for the variable order
`PCoord n` (block first, then column descending, then row ascending). `ord n` is the
resulting monomial order.

`antidiag n b k` is the squarefree monomial `∏ X ⟨b, p, q⟩` over the entries with
`p + q = n b - 1 + k` (the antidiagonal of the trailing `(n b - k)`-block of block `b`).
`CharpolyLeadingStatement n` says that, for `k < n b`, it is the leading monomial of the
coefficient of `t^k` of the characteristic polynomial of `genericBlock n b`, with a unit
leading coefficient.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

open MvPolynomial

variable {ι : Type} [Fintype ι] (n : ι → ℕ)

/-- The priority key of a coordinate: block index, then column (descending), then row. -/
def prio (c : Coord n) : Lex (ℕ × Lex (ℕᵒᵈ × ℕ)) :=
  toLex ((Fintype.equivFin ι c.1 : ℕ), toLex (OrderDual.toDual (c.2.2 : ℕ), (c.2.1 : ℕ)))

theorem prio_injective : Function.Injective (prio n) := by
  rintro ⟨b, p, q⟩ ⟨b', p', q'⟩ h
  simp only [prio, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
  obtain ⟨hb, hq, hp⟩ := h
  obtain rfl : b = b' := (Fintype.equivFin ι).injective (Fin.ext hb)
  obtain rfl : p = p' := Fin.ext hp
  obtain rfl : q = q' := Fin.ext hq
  rfl

/-- `Coord n` with the variable order used by `ord n`: `c < c'` iff `prio n c < prio n c'`. -/
def PCoord : Type := Coord n

instance : LinearOrder (PCoord n) := LinearOrder.lift' (prio n) (prio_injective n)

instance : Finite (PCoord n) := inferInstanceAs (Finite (Coord n))

instance : WellFoundedGT (PCoord n) := Finite.to_wellFoundedGT

theorem PCoord.lt_iff {c c' : PCoord n} : c < c' ↔ prio n c < prio n c' := Iff.rfl

/-- The weight of a coordinate: its column index. -/
def colWeight (c : PCoord n) : ℕ := (c.2.2 : ℕ)

/-- The monomial order on `Coord n →₀ ℕ`: weight by column index, ties broken
lexicographically for the variable order `PCoord n`. -/
def ord : MonomialOrder (Coord n) := weightLex (σ := PCoord n) (colWeight n)

open scoped MonomialOrder

theorem ord_lt_iff {a b : Coord n →₀ ℕ} :
    a ≺[ord n] b ↔
      Finsupp.weight (colWeight n) a < Finsupp.weight (colWeight n) b ∨
        (Finsupp.weight (colWeight n) a = Finsupp.weight (colWeight n) b ∧
          @toLex (PCoord n →₀ ℕ) a < @toLex (PCoord n →₀ ℕ) b) :=
  weightLex_lt_iff (σ := PCoord n) (colWeight n)

open Classical in
/-- The antidiagonal monomial of the trailing `(n b - k)`-block of block `b`: the product of
the variables `X ⟨b, p, q⟩` with `p + q = n b - 1 + k`. -/
def antidiag (b : ι) (k : ℕ) : Coord n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun c =>
    if c.1 = b ∧ (c.2.1 : ℕ) + c.2.2 = n b - 1 + k then 1 else 0

open Classical in
theorem antidiag_apply (b : ι) (k : ℕ) (c : Coord n) :
    antidiag n b k c = if c.1 = b ∧ (c.2.1 : ℕ) + c.2.2 = n b - 1 + k then 1 else 0 := rfl

/-- **Leading terms of the characteristic polynomial coefficients.** For `k < n b`, the
leading monomial for `ord n` of the coefficient of `t^k` of the characteristic polynomial of
`genericBlock n b` is `antidiag n b k`, and its leading coefficient is a unit. -/
def CharpolyLeadingStatement : Prop :=
  ∀ (b : ι) (k : ℕ), k < n b →
    (ord n).degree ((genericBlock n b).charpoly.coeff k) = antidiag n b k ∧
      IsUnit ((ord n).leadingCoeff ((genericBlock n b).charpoly.coeff k))

end Langlands.Archimedean.Kostant
