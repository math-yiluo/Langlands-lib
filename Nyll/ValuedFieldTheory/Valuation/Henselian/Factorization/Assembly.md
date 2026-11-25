# Hensel's lemma in factorization form over complete valuation rings

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file assembles the approximation argument into Hensel's lemma for a valuation ring `R` (a nontrivial `PreValuationRing` without zero divisors): a polynomial `f` over `R` whose reduction is nonzero and factors as a coprime product `ḡ · h̄` over the residue field factors as `f = G · H` over `R`, with `G` reducing to `ḡ`, `H` reducing to `h̄`, `deg G = deg ḡ` and `deg H ≤ deg f − deg ḡ`.

## Main results

- `henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing`: the statement above, for `R` precomplete and separated for the topology of its maximal ideal `m`.
- `henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing_principal`: the same, assuming instead that `R` is precomplete and separated for the `π`-adic topology of every nonzero `π ∈ m`.
- `henselFactorization_exists_limit_factorization_of_coprime_lifts_valuationRing` and its `_principal` form: versions starting from given lifts `g₀`, `h₀` of `ḡ`, `h̄` with `deg g₀ = deg ḡ = m'` and `deg h₀ ≤ d − m'`, where `deg f ≤ d`, and with the further hypotheses `ḡ.leadingCoeff ≠ 0` (`hglead`) and `m' ≤ d` (`hmd`); they give `G`, `H` with `deg G ≤ m'` and `deg H ≤ d − m'`.
- `henselFactorization_exists_degreeControlledLifts_of_residual_factorization`: over any local ring, if `f̄ ≠ 0` and `f̄ = ḡ · h̄`, there are lifts `g₀`, `h₀` with `deg g₀ = deg ḡ ≤ deg f` and `deg h₀ ≤ deg f − deg ḡ`.

## Proof

Lift a Bézout relation for `ḡ`, `h̄` to `a`, `b` over `R`. If the initial errors `f − g₀h₀` and `a g₀ + b h₀ − 1` vanish, `g₀`, `h₀` already work. Otherwise choose `π` among their coefficients so that both errors are divisible by `π` with `π ∈ m`, and apply a limit theorem of an imported file: the `m`-adic one for the first form, the `π`-adic one for the `_principal` form. The exact degree of `G` follows from the degree bound and the nonzero leading coefficient of `ḡ`.

## Caveats

- The polynomial `f` need not be monic, and `G`, `H` are not claimed to be monic.
- Separatedness for the `m`-adic topology is a strong hypothesis for a valuation ring: it fails whenever `m = m² ≠ 0`, as for non-discrete valuation rings of rank one. The `_principal` forms, with `π`-adic hypotheses, are the ones adapted to such rings.
- Completeness enters as explicit hypotheses (instances or functions `hpre`, `hhaus`), not through a Mathlib completeness class for valuations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/Assembly.lean`: the Lean file is the source byte for byte (SHA-256 `e4bee256c73a9bbd58a2baf2daea35707011c655de0bd222ce611e41eeefe2fd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
