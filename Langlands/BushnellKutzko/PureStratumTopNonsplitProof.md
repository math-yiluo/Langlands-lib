# BK93 (2.3.11): the top stratum of a pure stratum is nonsplit fundamental

The module `Langlands.BushnellKutzko.PureStratumTopNonsplitProof` proves the published
proposition `Langlands.BushnellKutzko.PureApproximation.TopNonsplitPremise` (module
`Langlands.BushnellKutzko.PureStratumApproximationSeed`), with independent universes `uF` for
the field and `uV` for the vector space.

```lean
theorem Langlands.BushnellKutzko.PureApproximation.topNonsplitPremise :
    TopNonsplitPremise.{uF, uV}
```

## What is proved

Let `F` be a nonarchimedean local field, `V` a finite-dimensional `F`-vector space and
`S = [𝓛, n, r, β]` a pure stratum (`Stratum.IsPure`). Then the stratum
`[𝓛, n, n - 1, β]` satisfies `Stratum.IsNonsplit`. That is:

- it is fundamental (`Stratum.IsFundamental`): its depth is `n - 1` and no element of the coset
  `β + 𝔓^{1-n}` is nilpotent;
- for some prime element `π` of `𝔬_F`, its polynomial `Stratum.fundamentalPolynomial` (the
  coefficientwise reduction of the `F`-characteristic polynomial of
  `y = π^{n/g} β^{e/g}`, where `e = e(𝓛)` and `g = gcd(e, n)`) equals `p ^ m` for a monic
  irreducible `p` over `𝔬_F / 𝔭_F` and some `m > 0`.

This is Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(2.3.11), printed p. 60 (PDF p. 72). Fundamentality is their (2.3.2), printed p. 57
(PDF p. 69). The polynomial `φ_b` and Definition (2.3.3) are on printed p. 58 (PDF p. 70).

## Declarations

Generic matrix lemmas, in `Langlands.BushnellKutzko`:

- `aeval_matrix_map_map`: evaluating polynomials at a matrix commutes with a ring
  homomorphism applied to the coefficients.
- `charpoly_dvd_pow_card_of_aeval_eq_zero`: over a commutative ring, if `q(A) = 0` for an
  `N × N` matrix `A`, then `charpoly A ∣ q ^ N`.
- `charpoly_eq_pow_of_aeval_pow_eq_zero`: over a field, if `p` is monic irreducible and
  `p(A)^e = 0` for a nonempty square matrix `A`, then `charpoly A = p ^ m` with `m > 0`.
- `reduceIntegralPolynomial_map`: if `O → K` is injective, then `reduceIntegralPolynomial`
  sends the image of `q ∈ O[X]` to the reduction of `q` modulo the Jacobson radical.

Lattice-chain lemmas, in `Langlands.BushnellKutzko.LatticeChain`:

- `reduceIntegralPolynomial_charpoly_eq_pow`: let `Y ∈ End_F(V)` map `L_0` into itself, and
  let `P ∈ 𝔬_F[X]` reduce to a monic irreducible polynomial modulo `𝔭_F`. If
  `P(Y)^e` maps `L_0` into `ϖ L_0` for a uniformizer `ϖ`, then the reduced characteristic
  polynomial of `Y` is a positive power of the reduction of `P`.
- `not_isNilpotent_of_fieldShift`: let `E` be a field acting on `V` whose units normalize
  `𝓛`. If a unit `u ∈ Eˣ` shifts the chain by `-n`, then no element of `u + 𝔓^{1-n}` is
  nilpotent.
- `exists_reduceIntegralPolynomial_charpoly_eq_pow`: in the same setting, if a unit of `E`
  shifts the chain by `0`, then its reduced characteristic polynomial (as an
  `F`-endomorphism of `V`) is `p ^ m` with `p` monic irreducible over `𝔬_F / 𝔭_F` and `m > 0`.

## Route of the Lean proof

Write `E = F[β]`. Purity makes `E` a field whose units lie in the stabilizer of `𝓛`, with
`v_𝓛(β) = -n`. In particular `β ≠ 0`, and `LatticeChain.valuation_eq_shift` shows that `β`
carries `L_i` onto `L_{i-n}`.

1. **Fundamental (`not_isNilpotent_of_fieldShift`).** Let `x = β + d` with
   `d ∈ 𝔓^{1-n}`, and suppose `x v = 0`. If `v ∈ L_i`, then `β v = -d v ∈ L_{i+1-n}`, so
   `v ∈ L_{i+1}`. Starting from some `L_{i_0}` containing `v`
   (`LatticeChain.exists_lattice_depth`), `v` lies in every lattice, hence `v = 0`
   (`LatticeChain.lattice_eq_zero_of_forall`). So `x` is injective. Since `V ≠ 0`, `x` is not
   nilpotent. This is the content of BK93 (2.3.2): `β + 𝔓^{1-n}` consists of units.
2. **A unit of shift zero.** Fix a uniformizer `ϖ` of `𝔬_F`; it is the prime element in
   `Stratum.IsNonsplit`. In `Eˣ` take `y = ϖ^{n/g} β^{e/g}`. Here `ϖ` shifts the chain by
   `e` (`LatticeChain.fieldShift_baseUniformizer`) and `β` by `-n`, so `y` shifts it by
   `(n/g)e - (e/g)n = 0`. Its image in `End_F(V)` is `Stratum.fundamentalElement`.
   `LatticeChain.exists_integerUnit_of_fieldShift_zero` makes `y` a unit of the integral
   closure `𝔬_E` of `𝔬_F` in `E` (`subfieldIntegers`), a discrete valuation ring
   (`subfieldIntegers_isDiscreteValuationRing`).
3. **The residue polynomial (`exists_reduceIntegralPolynomial_charpoly_eq_pow`).** The image of
   `ϖ` in `𝔬_E` is not a unit: a unit of `𝔬_E` shifts the chain by `0`
   (`LatticeChain.fieldShift_integerUnit`), and `ϖ` shifts it by `e > 0`. So `𝔬_F → 𝔬_E` induces
   `k_F = 𝔬_F / 𝔭_F → k_E`. Let `p` be the minimal polynomial over `k_F` of the residue class of
   `y` in `k_E`. It is monic and irreducible because `y` is integral over `𝔬_F` and `k_E` is a
   field. Take a monic lift `P ∈ 𝔬_F[X]` (`Polynomial.lifts_and_degree_eq_and_monic`). Then
   `P(y)` has residue `p(ȳ) = 0`, so `P(y) = c ϖ_E` with `c ∈ 𝔬_E` and `ϖ_E` a uniformizer of
   `𝔬_E`. As `ϖ_E` shifts the chain by a positive amount
   (`LatticeChain.fieldShift_uniformizer_pos`) and `c` preserves every lattice
   (`LatticeChain.subfieldInteger_smul_mem`), `P(y)` maps `L_i` into `L_{i+1}`. Hence `P(y)^e`
   maps `L_0` into `L_e = ϖ L_0`.
4. **The integral matrix (`reduceIntegralPolynomial_charpoly_eq_pow`).** The lattice `L_0` is
   free over `𝔬_F`, and a basis of it is an `F`-basis of `V`
   (`Module.Basis.extendOfIsLattice`). Since `y` preserves `L_0`, its matrix in this basis is
   the image of an integral matrix `A₀`. So the characteristic polynomial of `y` is the image
   of `charpoly A₀`, and by `reduceIntegralPolynomial_map` its reduction is the
   characteristic polynomial of `Ā₀ = A₀ mod 𝔭_F`. The entries of `P(A₀)^e` lie in `ϖ 𝔬_F`,
   so `p(Ā₀)^e = 0`.
5. **Power of an irreducible (`charpoly_eq_pow_of_aeval_pow_eq_zero`).** In `R[X][Y]`, `Y - X`
   divides `q(Y) - q(X)`. Evaluating `Y` at `A` gives a matrix factorization
   `q(X)·1 = (X·1 - A) H` over `R[X]` when `q(A) = 0`, and taking determinants gives
   `charpoly A ∣ q ^ N`. With `q = p^e` and `p` prime in `k_F[X]`, `dvd_prime_pow` makes
   `charpoly Ā₀` associated to a power `p ^ m`. Both are monic, so they are equal, and
   `m > 0` because the degree is `dim V > 0`.

## Relation to the source proof

BK93 deduce (2.3.11) from (2.3.2) and from the remark after (2.3.8): a stratum with a
splitting has `F[b]` not a field, by (2.3.5). They combine this with the construction
(2.3.9)–(2.3.10) of a splitting of a split fundamental stratum, which assumes
`gcd(n, e(𝔄)) = 1` and uses Hensel's lemma together with Kutzko's [K4] (3.4). The Lean proof
uses neither splittings nor Hensel's lemma, and it does not need `gcd(n, e) = 1`. Instead it
uses that `y = ϖ^{n/g} β^{e/g}` lies in `𝔬_E^×`. If `P` is a monic lift of the minimal
polynomial over `k_F` of the residue of `y`, then `P(y)` acts nilpotently on `L_0 / ϖ L_0`,
which forces the reduced characteristic polynomial to be a power of that minimal polynomial.

## Imports

- `Langlands.BushnellKutzko.PureStratumApproximationSeed`: the target statement
  `TopNonsplitPremise`, and through its imports `Stratum.IsPure`, `Stratum.IsNonsplit` and
  `Stratum.fundamentalPolynomial` (`Langlands.BushnellKutzko.FundamentalStratum`).
- `Langlands.BushnellKutzko.SubfieldValuationShifts`: field shifts of a normalizing field
  (`LatticeChain.fieldShift` and its lemmas), the integral closure `subfieldIntegers` as a
  discrete valuation ring, and `LatticeChain.exists_integerUnit_of_fieldShift_zero`.
- `Langlands.BushnellKutzko.AdjointLatticeBounds`: `LatticeChain.exists_lattice_depth`,
  `LatticeChain.lattice_eq_zero_of_forall` and `LatticeChain.uniformizer_lattice_mem_iff`.

The proof does not use `PureStratumSimpleApproximationStatement` or
`CriticalDerivedStratumStatement` (BK93 (2.4.1)(iii)).
