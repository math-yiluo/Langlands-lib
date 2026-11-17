import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.ENat.Basic

/-!
# The polar-part model `ν(n, f, s; q)` of the numerical local Langlands route

Operator route note `operator-numerical-llc-route-2026-11-16` (16 November 2026),
§3: Definition 3.1 (`def:model`, the polar-part model `𝒫(n, f, s; q)`, its
cardinality `ν(n, f, s; q)` and `τ(n, s; q) = ν(n, 1, s; q)`), Lemma 3.2
(`lem:nu`, closed formula), Lemma 3.3 (`lem:polar`, counting identity and its
converse), and Proposition 5.12 (`prop:LDcount`) (b), which uses the converse in a
truncated form. These are internal results of the route note, not numbered results
of Henniart (1988). Definitions and proposition definitions only; none of the
statements is proved here (the only proof is the Galois stability of `polarParts`).
-/

noncomputable section

namespace Langlands.Henniart

namespace Numerical

section Model

open Classical in
/-- The gcd of the positive exponents `{i ≥ 1 : c i ≠ 0}` of a map
`c : {0, …, m} → L`; it is `0` when that set is empty. -/
def polarSupportGcd {L : Type*} [Field L] {m : ℕ} (c : Fin (m + 1) → L) : ℕ :=
  (Finset.univ.filter fun i : Fin (m + 1) => 0 < (i : ℕ) ∧ c i ≠ 0).gcd fun i => (i : ℕ)

/-- Conditions (P1)–(P3) of route-note Definition 3.1 on `c : {0, …, m} → L`, with
`r = n / f`: `c 0 ≠ 0` and `c m ≠ 0`; the values of `c` generate `L` over `k`;
`gcd(r, {i ≥ 1 : c i ≠ 0}) = 1`, the gcd with the empty set being `r`. -/
def IsPolarPart (k : Type*) {L : Type*} [Field k] [Field L] [Algebra k L] (r m : ℕ)
    (c : Fin (m + 1) → L) : Prop :=
  c 0 ≠ 0 ∧ c (Fin.last m) ≠ 0 ∧ IntermediateField.adjoin k (Set.range c) = ⊤ ∧
    Nat.gcd r (polarSupportGcd c) = 1

/-- The maps `c : {0, …, m} → L` satisfying (P1)–(P3), as a `Gal(L/k)`-stable set;
`Gal(L/k)` acts on maps by `(g • c) i = g (c i)`. -/
def polarParts (k L : Type*) [Field k] [Field L] [Algebra k L] (r m : ℕ) :
    SubMulAction Gal(L/k) (Fin (m + 1) → L) where
  carrier := {c | IsPolarPart k r m c}
  smul_mem' g c hc := by
    obtain ⟨h0, hm, hgen, hgcd⟩ := hc
    have happ : ∀ i, (g • c) i = g (c i) := fun i => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [happ]
      exact (map_ne_zero g).mpr h0
    · rw [happ]
      exact (map_ne_zero g).mpr hm
    · have hrange : Set.range (g • c) = (g : L →ₐ[k] L) '' Set.range c := by
        rw [← Set.range_comp]
        rfl
      rw [hrange, ← IntermediateField.adjoin_map, hgen, ← AlgHom.fieldRange_eq_map]
      exact AlgEquiv.fieldRange_eq_top g
    · have hsupp : polarSupportGcd (g • c) = polarSupportGcd c := by
        unfold polarSupportGcd
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, happ]
        rw [map_ne_zero g]
      rw [hsupp]
      exact hgcd

/-- The polar-part model over a finite extension `L/k`: the set of
`Gal(L/k)`-orbits of maps `c : {0, …, m} → L` satisfying (P1)–(P3) with `r = n / f`
(route note, Definition 3.1, with `k = 𝔽_q`, `L = 𝔽_{q^f}`, `m = s / f`). -/
abbrev PolarPartModel (k L : Type*) [Field k] [Field L] [Algebra k L] (r m : ℕ) :
    Type _ :=
  MulAction.orbitRel.Quotient Gal(L/k) (polarParts k L r m)

/-- The number of elements of `PolarPartModel k L r m`. -/
def polarPartCountOf (k L : Type*) [Field k] [Field L] [Algebra k L] (r m : ℕ) : ℕ :=
  Nat.card (PolarPartModel k L r m)

end Model

/-- The field `𝔽_q` used for `q = p ^ a` (`p = q.minFac`, `a` the exponent of `p` in
`q`): `GaloisField p a`, which has `q` elements when `q` is a prime power. -/
abbrev polarBaseField (q : ℕ) [Fact q.minFac.Prime] : Type :=
  GaloisField q.minFac (q.factorization q.minFac)

/-- The field `𝔽_{q^f}` used for `q = p ^ a` and `f ≥ 1`: Mathlib's chosen degree-`f`
extension `FiniteField.Extension (polarBaseField q) p f` of `polarBaseField q`. -/
abbrev polarExtensionField (q f : ℕ) [Fact q.minFac.Prime] [NeZero f] : Type :=
  FiniteField.Extension (polarBaseField q) q.minFac f

/-- `ν(n, f, s; q)` of route-note Definition 3.1. If `q` is a prime power `p ^ a`,
`n ≥ 1`, `f ≥ 1`, `f ∣ n` and `f ∣ s`, it is the number of
`Gal(𝔽_{q^f}/𝔽_q)`-orbits of maps `c : {0, …, s / f} → 𝔽_{q^f}` satisfying (P1)–(P3)
with `r = n / f`, computed with `𝔽_q = polarBaseField q = GaloisField p a` and
`𝔽_{q^f} = polarExtensionField q f = FiniteField.Extension 𝔽_q p f`. In every other
case it is `0`. -/
def polarPartCount (q n f s : ℕ) : ℕ :=
  if h : IsPrimePow q ∧ 1 ≤ n ∧ 1 ≤ f ∧ f ∣ n ∧ f ∣ s then
    haveI : Fact q.minFac.Prime := ⟨Nat.minFac_prime h.1.ne_one⟩
    haveI : NeZero f := ⟨by omega⟩
    polarPartCountOf (polarBaseField q) (polarExtensionField q f) (n / f) (s / f)
  else 0

/-- `τ(n, s; q) = ν(n, 1, s; q)` of route-note Definition 3.1. -/
def polarTwistCount (q n s : ℕ) : ℕ :=
  polarPartCount q n 1 s

end Numerical

open Numerical ArithmeticFunction

/-- Route note, Lemma 3.2 (`lem:nu`), multiplied out over `ℤ`. For a prime power `q`
and `n ≥ 1`, `f ≥ 1`, `f ∣ n`, `f ∣ s`: if `s ≥ 1`, then with `m = s / f`,
`f · ν(n,f,s;q) = Σ_{i ∣ f} μ(f/i) (q^i − 1)² Σ_{e ∣ gcd(n/f, m)} μ(e) q^{i(m/e − 1)}`;
if `s = 0`, then `ν(n,f,0;q) = 0` for `f ≠ n`, and
`n · ν(n,n,0;q) = Σ_{i ∣ n} μ(n/i) (q^i − 1)`. -/
def PolarPartClosedFormulaStatement : Prop :=
  ∀ q : ℕ, IsPrimePow q → ∀ n f s : ℕ, 1 ≤ n → 1 ≤ f → f ∣ n → f ∣ s →
    (1 ≤ s →
      (f : ℤ) * (polarPartCount q n f s : ℤ) =
        ∑ i ∈ f.divisors, (moebius (f / i) * ((q : ℤ) ^ i - 1) ^ 2 *
          (∑ e ∈ (Nat.gcd (n / f) (s / f)).divisors,
            moebius e * (q : ℤ) ^ (i * (s / f / e - 1))))) ∧
    (s = 0 →
      (f ≠ n → polarPartCount q n f 0 = 0) ∧
        (n : ℤ) * (polarPartCount q n n 0 : ℤ) =
          ∑ i ∈ n.divisors, moebius (n / i) * ((q : ℤ) ^ i - 1))

/-- Route note, Lemma 3.3 (`lem:polar`), identity (`eq:polar`), multiplied by `f`
over `ℤ`: for a prime power `q`, `n ≥ 1`, `f ≥ 1`, `f ∣ n` and `j ≥ 0`,
`f · Σ_{d ∣ n/f} Σ_{s : f ∣ s, d s ≤ j} ν(n/d, f, s; q) =
Σ_{i ∣ f} μ(f/i) (q^i − 1) q^{i ⌊j/f⌋}`. Since `d ≥ 1`, the indices `s` with
`d s ≤ j` lie in `{0, …, j}`. -/
def PolarPartCountingIdentityStatement : Prop :=
  ∀ q : ℕ, IsPrimePow q → ∀ n f j : ℕ, 1 ≤ n → 1 ≤ f → f ∣ n →
    (f : ℤ) * (∑ d ∈ (n / f).divisors,
        ∑ s ∈ (Finset.range (j + 1)).filter (fun s => f ∣ s ∧ d * s ≤ j),
          (polarPartCount q (n / d) f s : ℤ)) =
      ∑ i ∈ f.divisors, moebius (f / i) * ((q : ℤ) ^ i - 1) * (q : ℤ) ^ (i * (j / f))

/-- The converse of route-note Lemma 3.3 for `f = 1`, in the truncated form used in
the proof of Proposition 5.12 (`prop:LDcount`) (b). For a prime power `q`, a bound
`e` and `T : ℕ → ℕ → ℕ∞` (rank, Swan exponent): if
`Σ_{d ∣ n} Σ_{k ≥ 0, n k ≤ d j} T d k = (q − 1) q^j` in `ℕ∞` for all `n ≥ 1` and
`j < n e`, then `T n s = τ(n, s; q)` for all `n ≥ 1` and `s < n e`. Since `d ∣ n`,
the indices `k` with `n k ≤ d j` lie in `{0, …, j}`. -/
def PolarPartTruncatedUniquenessStatement : Prop :=
  ∀ q : ℕ, IsPrimePow q → ∀ (e : ℕ) (T : ℕ → ℕ → ℕ∞),
    (∀ n j : ℕ, 1 ≤ n → j < n * e →
      (∑ d ∈ n.divisors, ∑ k ∈ (Finset.range (j + 1)).filter (fun k => n * k ≤ d * j),
          T d k) = (((q - 1) * q ^ j : ℕ) : ℕ∞)) →
    ∀ n s : ℕ, 1 ≤ n → s < n * e → T n s = (polarTwistCount q n s : ℕ∞)

end Langlands.Henniart
