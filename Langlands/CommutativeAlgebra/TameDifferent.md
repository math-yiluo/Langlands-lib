# Traces on Artinian local algebras and the tame different

Module `Langlands.CommutativeAlgebra.TameDifferent`, namespace
`Langlands.CommutativeAlgebra.TameDifferent`. It imports `Langlands.MathlibBase` and
`Langlands.LocalFactor.BrauerKernel.Trace` (for
`Langlands.LocalFactor.BrauerKernel.trace_eq_trace_restrict_add_trace_mapQ`, the additivity of
the trace of an endomorphism over an invariant subspace), and no module of weil-conjectures.

The main result is the tame case of Serre, *Local Fields*, III §6, Prop. 13 (p. 58), for an
extension of Dedekind domains: if the ramification index `e` of a prime `P` is nonzero in the
residue field below and the residue extension is separable, the exponent of `P` in the different
ideal is `e - 1`.

## Traces on modules of finite length

`smulEnd k M r : M →ₗ[k] M` is multiplication by `r : R` on an `R`-module `M`, as a `k`-linear
map, for a `k`-algebra `R` with `IsScalarTower k R M`.

| Declaration | Statement |
|---|---|
| `trace_smulEnd_eq_of_linearEquiv` | an `R`-linear equivalence `M ≃ M'` preserves the `k`-trace of `smulEnd k _ r` |
| `trace_smulEnd_eq_add` | for a submodule `N` of a finite-dimensional `M`, the trace on `M` is the trace on `N` plus the trace on `M ⧸ N` |
| `trace_smulEnd_bot` | the trace on the zero submodule is `0` |
| `trace_smulEnd_quotient_maximalIdeal` | for `R` local, the trace on `R ⧸ 𝔪_R` is `Algebra.trace k (R ⧸ 𝔪_R)` of the class of `r` |
| `trace_smulEnd_covBy` | for submodules `p ⋖ q` (`q / p` simple) of a finite-dimensional `M` over a local `R`, the trace on `q` is the trace on `p` plus the residue trace of `r` |
| `trace_smulEnd_eq_length_nsmul` | for `R` local and `M` finite-dimensional over `k`: `trace_k(r on M) = (length_R M) • Tr_{(R ⧸ 𝔪_R)/k}(r̄)` |

The proof of `trace_smulEnd_eq_length_nsmul` takes a composition series of `M`
(`isFiniteLength_iff_exists_compositionSeries`; `M` has finite length because it is
finite-dimensional over `k`) and adds the traces along it with `trace_smulEnd_covBy`: each simple
subquotient is isomorphic to `R ⧸ 𝔪_R` (`isSimpleModule_iff_quot_maximal`), and the number of
steps is the length (`Module.length_compositionSeries`).

## The trace on `B ⧸ P ^ n`

`trace_quotient_pow`: let `B` be a Dedekind domain, finite over `A`, `P ≠ ⊥` a maximal ideal of
`B` over a maximal ideal `p` of `A` and `n` with `p ≤ (P ^ n).comap (algebraMap A B)`. For the
`A ⧸ p`-algebra structure `Ideal.Quotient.algebraQuotientOfLEComap` of `B ⧸ P ^ n`,

```lean
Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ x) =
  n • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ x)
```

Proof: for `n = 0` the ring `B ⧸ P ^ 0 = B ⧸ B` is the zero ring, so the trace on the left is
`0`, as is `0 • Tr_{(B ⧸ P)/(A ⧸ p)}(x̄)` on the right. Let `n > 0`. Then `B ⧸ P ^ n` is
isomorphic, as an `A ⧸ p`-algebra, to `R = S ⧸ 𝔪_S ^ n` with `S` the localization of `B` at `P`,
a discrete valuation ring (`IsLocalization.AtPrime.equivQuotMaximalIdealPow`,
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`). The ring `R` is local (it
is nonzero as `n > 0`) of length `n` over itself
(`IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`) and its residue field is `B ⧸ P`, so
`trace_smulEnd_eq_length_nsmul` gives the formula.

## The tame different

Variables: Dedekind domains `A` and `B`, `B` torsion-free and finite over `A`, a maximal ideal
`p` of `A` and a maximal ideal `P` of `B` with `P.LiesOver p`; `e = P.ramificationIdx A` is
Mathlib's ramification index (`Ideal.ramificationIdx`). The first three theorems assume
`Algebra.IsSeparable (FractionRing A) (FractionRing B)` for the algebra structure
`FractionRing.liftAlgebra`, the form of the hypothesis in Mathlib's
`Mathlib/RingTheory/DedekindDomain/Different.lean`.

| Declaration | Statement |
|---|---|
| `pow_ramificationIdx_sub_one_dvd_differentIdeal` | `p ≠ ⊥ → P ^ (e - 1) ∣ differentIdeal A B` |
| `not_pow_ramificationIdx_dvd_differentIdeal` | if `p ≠ ⊥`, `B ⧸ P` is separable over `A ⧸ p` and `(e : A ⧸ p) ≠ 0`, then `¬ P ^ e ∣ differentIdeal A B` |
| `count_normalizedFactors_differentIdeal` | under the same hypotheses, `(normalizedFactors (differentIdeal A B)).count P = e - 1` |
| `isSeparable_fractionRing` | for fraction fields `K` of `A` and `L` of `B` with `IsScalarTower A K L` and `IsScalarTower A B L`, `Algebra.IsSeparable K L` implies `Algebra.IsSeparable (FractionRing A) (FractionRing B)` |
| `count_normalizedFactors_differentIdeal_of_isSeparable` | `count_normalizedFactors_differentIdeal` with the hypothesis `Algebra.IsSeparable K L` in place of the separability of the `FractionRing`s |

Proofs:

- `pow_ramificationIdx_sub_one_dvd_differentIdeal` writes `p B = P ^ e * Q` with `P ∤ Q`
  (`Ideal.eq_prime_pow_mul_coprime`, the exponent being `e` by
  `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`) and applies Mathlib's
  `pow_sub_one_dvd_differentIdeal`.
- `not_pow_ramificationIdx_dvd_differentIdeal` follows Serre's characterization of the
  different by traces (*Local Fields*, III §3) through Mathlib's
  `not_dvd_differentIdeal_of_intTrace_notMem`: it suffices to find `y ∈ Q` whose trace
  `Algebra.intTrace A B y` is not in `p`. By the Chinese remainder theorem
  `B ⧸ p B ≅ B ⧸ P ^ e × B ⧸ Q` (`Ideal.quotientMulEquivQuotientProd`). Since `B ⧸ P` is
  separable over `A ⧸ p`, some `x` has `Tr_{(B ⧸ P)/(A ⧸ p)}(x̄) ≠ 0` (`Algebra.trace_ne_zero`);
  take `y` with image `(x̄, 0)`. The trace of `y` reduced mod `p` is the trace on `B ⧸ p B`
  (`Algebra.trace_quotient_eq_of_isDedekindDomain`), which is the sum of the traces on the two
  factors (`Algebra.trace_prod_apply`): `e • Tr_{(B ⧸ P)/(A ⧸ p)}(x̄) + 0` by
  `trace_quotient_pow`, nonzero because `e ≠ 0` in the field `A ⧸ p`.
- `count_normalizedFactors_differentIdeal` combines the two through
  `emultiplicity_eq_count_normalizedFactors` and `pow_dvd_iff_le_emultiplicity`; the different is
  nonzero (`differentIdeal_ne_bot`) and `e ≠ 0` since `(e : A ⧸ p) ≠ 0`.
- `isSeparable_fractionRing` transports separability along the isomorphisms
  `FractionRing.algEquiv A K` and `FractionRing.algEquiv B L` (`Algebra.IsSeparable.of_equiv_equiv`),
  the compatibility of the maps being checked on `A` (`IsLocalization.ringHom_ext`), as in the
  proof of Mathlib's `coeSubmodule_differentIdeal`.

Serre proves Prop. 13 differently, after localizing and completing, from an Eisenstein equation
of a uniformizer; the trace argument above needs neither completion nor a reduction to the
totally ramified case. Serre's proposition also states the converse (if `e` is divisible by the
residue characteristic, `P ^ e` divides the different), which this module does not contain.
