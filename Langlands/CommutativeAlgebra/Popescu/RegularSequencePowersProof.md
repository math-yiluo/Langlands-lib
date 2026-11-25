# Proof of Stacks Lemma 10.68.9: powers of a regular sequence

`Langlands.CommutativeAlgebra.Popescu.regularSequencePowers :
RegularSequencePowersStatement.{u}` proves the Library statement
`Langlands.CommutativeAlgebra.Popescu.RegularSequencePowersStatement` (Stacks Project,
Chapter 10 *Commutative Algebra*, version ed88ff78, Lemma 10.68.9, Tag 07DV). For a
commutative ring `R : Type u`, an `R`-module `M : Type u`, `f : Fin r → R` and
`e : Fin r → ℕ` with every `e i > 0`, it shows

`RingTheory.Sequence.IsRegular M (List.ofFn f) ↔
  RingTheory.Sequence.IsRegular M (List.ofFn fun i => f i ^ e i)`.

`IsRegular` is Mathlib's notion: the sequence is weakly regular and `M/(f)M ≠ 0`. The theorem
has no hypotheses beyond those of the statement. The module imports only the statement module,
which imports `Mathlib.RingTheory.Regular.RegularSequence`. It uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Helper lemmas (namespace `Langlands.CommutativeAlgebra.Popescu.RegularSequencePowers`)

Write `M/aM` for `QuotSMulTop a M = M ⧸ a • ⊤`. The helper lemmas hold for modules in any
universe.

- `mk_eq_zero_iff`: the class of `m` in `M/aM` vanishes iff `m = a n` for some `n : M`.
- `isSMulRegular_quot_swap`: if `f` is `M`-regular and `g` is regular on `M/fM`, then `f` is
  regular on `M/gM`.
  - Suppose `f m = g n`. Then `g n ∈ fM`, so `n = f n'`, because `g` is regular on `M/fM`.
  - Hence `f m = f (g n')`, and `m = g n'` because `f` is regular.
- `isSMulRegular_quot_pow_of`: for `f` regular on `M`, if `g` is regular on `M/fM`, then it is
  regular on `M/f^{e+1}M`. The proof is by induction on `e`. Suppose `g m = f^{e+2} n`.
  - Then `g m ∈ fM`, so `m = f m'`.
  - Then `f (g m') = f (f^{e+1} n)`, so `g m' = f^{e+1} n` because `f` is regular.
  - By induction `m' ∈ f^{e+1}M`, so `m ∈ f^{e+2}M`.
- `isSMulRegular_quot_of_pow`: for `f` regular on `M`, if `g` is regular on `M/f^{e+1}M`, then
  it is regular on `M/fM`. Suppose `g m = f n`.
  - Then `g (f^e m) = f^{e+1} n`, so `f^e m = f^{e+1} p` for some `p`.
  - Since `f^e` is regular (`IsSMulRegular.pow`), `m = f p`.
- `pow_smul_top_eq_top` and `nontrivial_quot_pow_iff`: `M/f^{e+1}M` is nontrivial iff `M/fM`
  is. If `fM = M` then `f^{e+1}M = M`. Conversely `f^{e+1}M ⊆ fM`.
- `isRegular_nil_iff`: the empty sequence is `N`-regular iff `N` is nontrivial.
- `swapEquiv`: an `R`-linear isomorphism `(M/aM)/b(M/aM) ≅ (M/bM)/a(M/bM)`. Both sides are
  identified with `M/(aM + bM)` by `Submodule.quotientQuotientEquivQuotientSup` and
  `Submodule.map_pointwise_smul`.

## The key induction

`isRegular_quot_pow_iff`: let `f` be regular on `M` and let `g` be any list. Then `g` is regular
on `M/f^{e+1}M` iff it is regular on `M/fM`. The proof is by induction on `g`, for all modules
`M` at once.

- **Empty list.** This is `isRegular_nil_iff` together with `nontrivial_quot_pow_iff`.
- **`g = g₁ :: g'`.** By `isRegular_cons_iff`, `g₁ :: g'` is regular on `N` iff `g₁` is
  regular on `N` and `g'` is regular on `N/g₁N`.
  - `isSMulRegular_quot_of_pow` and `isSMulRegular_quot_pow_of` transfer the regularity of `g₁`
    in both directions.
  - Once `g₁` is regular on `M/fM`, `isSMulRegular_quot_swap` shows that `f` is regular on
    `M/g₁M`.
  - `swapEquiv` and `LinearEquiv.isRegular_congr` identify regularity of `g'` on
    `(M/f^{e+1}M)/g₁` and on `(M/fM)/g₁` with regularity on `(M/g₁M)/f^{e+1}` and on
    `(M/g₁M)/f`. The induction hypothesis for the module `M/g₁M` gives the equivalence.

## Main theorem

`powers_aux` proves the statement for modules in any universe, by induction on `r`.

- **`r = 0`.** Both lists are empty, and `simp` closes the goal.
- **Step.** Write `List.ofFn f = f₀ :: List.ofFn (f ∘ Fin.succ)` (`List.ofFn_succ`), and
  `e₀ = k + 1`. By `isRegular_cons_iff`, both sides split into the regularity of the head and
  the regularity of the tail on the quotient by the head.
  - `f₀` is `M`-regular iff `f₀^{k+1}` is. One direction is `IsSMulRegular.pow`. For the other,
    `f₀^{k+1} = f₀^k · f₀` and `IsSMulRegular.of_mul`.
  - The induction hypothesis, applied to the module `M/f₀M`, exchanges the tail `f₁, …` for the
    tail of powers `f₁^{e₁}, …`.
  - `isRegular_quot_pow_iff` then exchanges `M/f₀M` for `M/f₀^{k+1}M`.

`regularSequencePowers` specializes `powers_aux` to `R M : Type u`.

## Relation to the source proof

The source proof inducts on `r` and on the exponent, and uses the short exact sequences
`0 → M/fM → M/f^eM → M/f^{e−1}M → 0` with Lemma 10.68.8 (Tag 0F1T). The Lean proof uses no
short exact sequences. It checks regularity of single elements on `M/f^{e+1}M` and on `M/fM`
by direct element computations. For the remaining terms of the sequence it inducts on the list
and moves `f` past each term with `isSMulRegular_quot_swap` and `swapEquiv`.
