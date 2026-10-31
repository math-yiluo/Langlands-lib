# A coordinate change making a power series regular in the first variable

Helper module `Langlands.CommutativeAlgebra.MvPowerSeriesCoordinateChange`, written as part of
the proof that every stalk of a scheme smooth over an algebraically closed field is a unique
factorization domain (task `7d63b52e-e715-47d0-a015-331cfa8a4b6d`). It provides the
coordinate-change step in the proof that `K⟦X_0, …, X_n⟧` is a unique factorization domain.
After this step the Weierstrass preparation theorem applies in the variable `X 0`.

## Main result

`exists_algEquiv_coeff_single_zero_ne_zero`: let `K` be a commutative ring and `f` a nonzero
element of `MvPowerSeries (Fin (n + 1)) K`. Then there is a `K`-algebra automorphism `φ` of
`MvPowerSeries (Fin (n + 1)) K` and a `k : ℕ` such that the coefficient of `φ f` at the
monomial `X 0 ^ k` (exponent `Finsupp.single 0 k`) is nonzero.

No field hypothesis is needed. The automorphism is the substitution `X 0 ↦ X 0` and
`X i ↦ X i + X 0 ^ (s ^ i)` for `i ≠ 0`, for a suitable `s ≥ 1`. Substitutions of this kind
are the usual tool in proofs that power series rings over a field are factorial. The
statement and the proof here were written for this task and are not quoted from a source.

## Construction and proof

1. **Digit estimates (section `Weight`).** For `α : Fin m → ℕ` with every `α i < s`,
   `∑ i, α i * s ^ i < s ^ m` (`sum_mul_pow_lt`). Suppose also that `α` is
   colexicographically smaller than `d`: there is an index `i` with `α i < d i` and
   `α j = d j` for every `j > i`. Then `∑ α i * s ^ i < ∑ d i * s ^ i`
   (`sum_mul_pow_lt_of_colex`). Both proofs are induction on `m`, splitting off the last
   index with `Fin.sum_univ_castSucc`.

2. **The automorphism.** `coordFamily s c` is the family `X 0 ↦ X 0`,
   `X i ↦ X i + c • X 0 ^ (s ^ i)` for `i ≠ 0`. For `s ≠ 0` every member has zero constant
   coefficient, so it can be substituted (`hasSubst_coordFamily`). Substituting
   `coordFamily s d` into `coordFamily s c` gives `coordFamily s (c + d)`
   (`subst_coordFamily_coordFamily`). By `subst_comp_subst_apply`, substitution by `c`
   followed by substitution by `d` is substitution by `c + d` (`subst_coordFamily_subst`).
   `coordFamily s 0` is the family of variables (`coordFamily_zero`), and substituting the
   variables is the identity (`subst_self`). So substitution by `-c` undoes substitution
   by `c` (`subst_coordFamily_inv`). `coordChange hs` is the `K`-algebra automorphism
   `AlgEquiv.ofAlgHom` built from the substitution homomorphisms for `1` and `-1`, and
   `coordChange_apply` says it acts by substitution of `coordFamily s 1`.

3. **Reading off coefficients at `X 0 ^ k`.** `restrictFamily` substitutes `X 0 ↦ X` and
   `X i ↦ 0` for `i ≠ 0` into power series in one variable (`MvPowerSeries Unit K`). The
   coefficient of `X ^ k` in the result equals the coefficient of `g` at `X 0 ^ k`
   (`coeff_subst_restrictFamily`). This is computed with `coeff_subst` and
   `finsum_eq_single`. An exponent vector `d` with `d i ≠ 0` for some `i ≠ 0` contributes
   a factor `0 ^ (d i) = 0`. An exponent `single 0 j` with `j ≠ k` contributes the
   coefficient of `X ^ k` in `X ^ j`, which is zero.

4. **Composite substitution.** Substituting `restrictFamily` after `coordFamily s 1` equals
   the substitution `powFamily s : X i ↦ X ^ (s ^ i)` (`subst_restrictFamily_coordFamily`).
   Its coefficient of `X ^ k` is `∑ᶠ d, coeff d f • [expWeight s d = k]`, where
   `expWeight s d = ∑ i, d i * s ^ i` (`coeff_subst_powFamily`). The proof writes
   `d.prod (fun i e => (X ^ (s ^ i)) ^ e)` as `X ^ (∑ i, s ^ i * d i)` using
   `Finsupp.prod_fintype` and `Finset.prod_pow_eq_pow_sum`, and then applies `coeff_X_pow`.

5. **Main theorem.** Pick an exponent `d₀` with nonzero coefficient
   (`ne_zero_iff_exists_coeff_ne_zero`). Let `α` be minimal among the exponents with
   nonzero coefficient, for the well-founded order `Colex (Fin (n + 1) → ℕ)` (index
   `n` most significant), via `WellFounded.has_min` of the inverse image of `toColex`. Set
   `s = ∑ i, α i + 1`, so that every `α i < s`, and `k = expWeight s α`. If an exponent
   `d ≠ α` has nonzero coefficient, minimality and trichotomy of the colex linear order
   give `toColex α < toColex d`. Step 1 then gives `expWeight s α < expWeight s d`. So in
   the sum of step 4 only `d = α` contributes, and the coefficient of `X 0 ^ k` in
   `coordChange hs f` is `coeff α f ≠ 0`.

## Checks

The module compiles under a Lake build with no errors or warnings. The axioms of the main
theorem are `propext`, `Classical.choice` and `Quot.sound`.
