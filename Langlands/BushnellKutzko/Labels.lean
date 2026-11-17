import Mathlib.Algebra.IsPrimePow
import Langlands.Correspondence.HenniartPolarPart
import Langlands.FieldTheory.IrreduciblePolynomialLabels

/-!
# The label sets of Bushnell–Kutzko 1994

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes* (Contemp. Math. 177,
1994), (1.13) on printed pp. 115–116 and (3.7) with the paragraph after it on printed
pp. 125–126. The field `𝔽_{q^D}` is `polarExtensionField q D` of Task 7369. See the paired
Markdown file for the encoding.
-/

namespace Langlands.BushnellKutzko

open Polynomial Langlands.Henniart.Numerical Langlands.FieldTheory

/-- Use `q` as the field parameter except at `q = 1`, where an arbitrary field is needed
only to give the empty label sets an ambient type. -/
def labelFieldSize (q : ℕ) : ℕ := if q = 1 then 2 else q

instance labelFieldSize_minFac_prime (q : ℕ) : Fact (labelFieldSize q).minFac.Prime :=
  ⟨Nat.minFac_prime (by
    unfold labelFieldSize
    split_ifs <;> simp_all)⟩

/-- A polynomial over one of the fields `𝔽_{q^D}` (`D ≥ 1`), recorded together with the
exponent `D`. At `q = 1` the ambient fields instead use the parameter `2`. -/
structure FieldPolynomial (q : ℕ) where
  /-- The exponent `D`, so that `poly` is a polynomial over `𝔽_{q^D}`. -/
  exponent : ℕ+
  /-- The polynomial, over `polarExtensionField (labelFieldSize q) D = 𝔽_{q^D}` for
  prime powers `q`. -/
  poly : (polarExtensionField (labelFieldSize q) exponent)[X]

/-- One quadruple `(φᵢ(X), nᵢ, dᵢ, eᵢ)` of a label (BK94 (1.13)). The polynomial `φᵢ` is
recorded with the exponent `D` of the field `𝔽_{q^D}` that contains its coefficients; in a
label, (1.13) forces `D = d₀ d₁ ⋯ d_{i-1}`. -/
structure LabelEntry (q : ℕ) where
  /-- The polynomial `φᵢ(X)`, with its field exponent. -/
  polynomial : FieldPolynomial q
  /-- The level `nᵢ`. -/
  level : ℕ
  /-- The degree `dᵢ`. -/
  degree : ℕ
  /-- The number `eᵢ`. -/
  ramification : ℕ

/-- A finite sequence `((φᵢ(X), nᵢ, dᵢ, eᵢ))_{0 ≤ i ≤ r}` of label entries, `r ≥ 0`. -/
structure Label (q : ℕ) where
  /-- The last index `r`. -/
  r : ℕ
  /-- The entries, indexed by `0 ≤ i ≤ r`. -/
  entry : Fin (r + 1) → LabelEntry q

namespace Label

variable {q : ℕ}

/-- The partial product `d₀ d₁ ⋯ d_{i-1}` of the degrees of the entries of index `< i` (the
empty product `1` for `i = 0`). -/
def degreeProd (p : Label q) (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin (p.r + 1) => (j : ℕ) < i), (p.entry j).degree

/-- `e(p) = e_r` (BK94, printed p. 116). -/
def e (p : Label q) : ℕ := (p.entry (Fin.last p.r)).ramification

/-- `d(p) = d₀ d₁ ⋯ d_r` (BK94, printed p. 116). -/
def d (p : Label q) : ℕ := ∏ j, (p.entry j).degree

/-- `f(p) = b / d(p)` (BK94, printed p. 116); it depends on the parameter `b` of the label set. -/
def f (p : Label q) (b : ℕ) : ℕ := b / p.d

end Label

/-- The set `P^m_n(a, b; q)` of BK94 (1.13), for natural numbers `m < n`, positive integers
`a`, `b` and a prime power `q`; it is empty outside this range. -/
def labelSet (m n a b q : ℕ) : Set (Label q) :=
  {p | IsPrimePow q ∧ m < n ∧ 0 < a ∧ 0 < b ∧
    -- (1.13)(i): `dᵢ` and `eᵢ` are positive (the levels are natural numbers).
    (∀ i, 0 < (p.entry i).degree ∧ 0 < (p.entry i).ramification) ∧
    -- (1.13)(ii)(a)–(d); the polynomial `φ₀` lies over `𝔽_q = 𝔽_{q^1}`.
    (p.entry 0).level = n ∧
    (p.entry 0).degree ∣ b ∧
    (p.entry 0).ramification = Nat.gcd (p.entry 0).level a ∧
    ((p.entry 0).polynomial.exponent : ℕ) = 1 ∧
    (p.entry 0).polynomial.poly ∈ irreduciblePolynomialLabels (p.entry 0).degree
      (polarExtensionField (labelFieldSize q) (p.entry 0).polynomial.exponent) ∧
    -- (1.13)(iii), for the entry of index `i + 1`, `0 ≤ i < r`; the polynomial `φ_{i+1}` lies
    -- over `𝔽_{q^{d₀ ⋯ dᵢ}}`.
    ∀ i : Fin p.r,
      m < (p.entry i.succ).level ∧
      (p.entry i.succ).level < (p.entry i.castSucc).level ∧
      p.degreeProd ((i : ℕ) + 2) ∣ b ∧
      (p.entry i.succ).ramification =
        Nat.gcd (p.entry i.succ).level (p.entry i.castSucc).ramification ∧
      ((p.entry i.succ).polynomial.exponent : ℕ) = p.degreeProd ((i : ℕ) + 1) ∧
      (p.entry i.succ).polynomial.poly ∈
        irreduciblePolynomialLabels (p.entry i.succ).degree
          (polarExtensionField (labelFieldSize q) (p.entry i.succ).polynomial.exponent)}

/-- `P_n(a, b; q) = P^0_n(a, b; q)` (BK94, printed p. 125); empty for `n = 0`. -/
def bottomLabelSet (n a b q : ℕ) : Set (Label q) := labelSet 0 n a b q

/-- `P̃_n(a, b; q) = {(p, φ) : p ∈ P_n(a, b; q), φ ∈ 𝔍(f(p), q^{d(p)})}` for `n ≥ 1`
(BK94, printed p. 125); empty for `n = 0`. The polynomial `φ` is recorded with its field
exponent, which must be `d(p)`. -/
def extendedLabelSet (n a b q : ℕ) : Set (Label q × FieldPolynomial q) :=
  {x | x.1 ∈ bottomLabelSet n a b q ∧
    (x.2.exponent : ℕ) = x.1.d ∧
    x.2.poly ∈ irreduciblePolynomialLabels (x.1.f b)
      (polarExtensionField (labelFieldSize q) x.2.exponent)}

/-- `P̃_0(a, b; q) = 𝔍(b, q)` (BK94, printed p. 126), over `𝔽_q = 𝔽_{q^1}`; it does not depend
on `a`, and it is empty when `q` is not a prime power. -/
def degenerateLabelSet (b q : ℕ) : Set (polarExtensionField (labelFieldSize q) 1)[X] :=
  {φ | IsPrimePow q ∧
    φ ∈ irreduciblePolynomialLabels b (polarExtensionField (labelFieldSize q) 1)}

end Langlands.BushnellKutzko
