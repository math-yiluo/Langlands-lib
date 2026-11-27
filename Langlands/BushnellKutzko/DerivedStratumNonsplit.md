# Nonsplit strata from a residue image without zero divisors

This module gives a sufficient condition for a fundamental stratum over a
discrete valuation ring to be nonsplit (Definition (2.3.3) of BK93). It is used
for derived strata, whose integer ring is `subfieldIntegers F E`. All results
are proved.

## Characteristic polynomials over a discrete valuation ring

Let `O` be a discrete valuation ring with fraction field `K`, and let `𝓛` be an
`O`-lattice chain in a finite-dimensional `K`-vector space.

- `LatticeChain.reduceIntegralPolynomial_charpoly_eq_pow_of_dvr`: let `Y`
  preserve `L₀` and let `P ∈ O[X]` reduce to a monic irreducible polynomial. If
  `P(Y)^e` maps `L₀` into `ϖ L₀` for a uniformizer `ϖ`, then the reduced
  characteristic polynomial of `Y` is a positive power of the reduction of `P`.
  The proof is that of `LatticeChain.reduceIntegralPolynomial_charpoly_eq_pow`
  in `PureStratumTopNonsplitProof`, which treats `O = 𝒪[F]`. Here it runs over an
  arbitrary discrete valuation ring: the matrix of `Y` on a basis of `L₀` is
  integral, and its reduction is killed by a power of `P mod 𝔭`.
- `LatticeChain.exists_monic_charpoly_eq_map`: the characteristic polynomial of
  an endomorphism preserving `L₀` is the image of a monic polynomial over `O`.

## Filtration arithmetic and shifting units

For a lattice chain over an arbitrary ring `O`:

- `pow_mem_endFiltration_mul`: `x ∈ 𝔓^s` gives `x^k ∈ 𝔓^{ks}`.
- `pow_sub_pow_mem_endFiltration`: let `x, x' ∈ 𝔓^s` with `x − x' ∈ 𝔓^{s+1}`.
  Then `x^k − x'^k ∈ 𝔓^{ks+1}`.
- `mul_sub_mul_mem_endFiltration`: the analogous congruence for products.
- `mem_endFiltration_stabilizer_iff`: a unit `g ∈ 𝔎(𝔄)` lies in `𝔓^n` exactly
  when `n` is at most its shift `v_𝔄(g)`.
- `inv_mem_order_of_not_mem`: let `g ∈ 𝔎(𝔄)` lie in `𝔄` but not in `𝔓`. Then
  `v_𝔄(g) = 0`, so `g⁻¹ ∈ 𝔄`.
- `residue_mul_eq_zero`: let `R` be a subring of `End_K(V)` whose nonzero
  elements are units of `𝔎(𝔄)`. Then the image of `R ∩ 𝔄` in `𝔄/𝔓` has no zero
  divisors. A nonzero class of this image is invertible in `𝔄/𝔓`, by the
  preceding item.
- `Stratum.algebraMap_mem_firstFiltrationIdeal`: scalars from the maximal ideal
  of `O` lie in `𝔓`.

## The criterion

`Stratum.isNonsplit_of_residue_domain` takes a fundamental stratum `D` over a
discrete valuation ring and a prime element `π` with `y_b ∈ 𝔄`; here
`y_b = Stratum.fundamentalElement D π`. It also takes a ring homomorphism `f`
from the order with kernel exactly `𝔓`, and a subring `S` of its target
without zero divisors that contains `f(y_b)` and the images of the scalars.
Then `D.IsNonsplit`.

The proof evaluates polynomials over the residue field `k` at `f(y_b)`, giving a
homomorphism `k[X] → S`. Its kernel is a prime ideal. It is nonzero because it
contains the reduction of a monic integral characteristic polynomial of `y_b`,
by Cayley–Hamilton. Its monic generator `p` is irreducible. A monic lift `P` of
`p` satisfies `f(P(y_b)) = 0`, so `P(y_b) ∈ 𝔓` and `P(y_b)^e` maps `L₀` into
`π L₀`, where `e` is the period. The first result then gives
`φ_b = p^m` with `m > 0`.

Source: Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), §2.3, Definition (2.3.3) and the construction of `φ_b`,
printed pp. 57–58 (PDF pp. 69–70), literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The
residue-domain criterion is an internal device. It replaces the comparison of
characteristic polynomials in the proof of Lemma (5.3) of Bushnell and Kutzko,
*Simple types in GL(N): computing conjugacy classes* (1994), printed p. 133.
