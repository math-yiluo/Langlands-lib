# Proof of the unramified computation of Rankin–Selberg integrals

Author: Worker 1797. Module `Langlands.Representation.RankinSelberg.UnramifiedPairProof`.

```lean
theorem Langlands.RankinSelberg.unramifiedPair :
    UnramifiedPairStatement.{uF, uV, uW}
```

This proves the unchanged Library proposition
`Langlands.RankinSelberg.UnramifiedPairStatement` (module
`Langlands.Representation.RankinSelberg.UnramifiedPairStatement`). It is the conjunction
of:

- (A) `UnramifiedSphericalVectorStatement`: unique normalized spherical Whittaker
  vectors, for both `ψ` and `ψ⁻¹`, in every Whittaker model of an irreducible admissible
  generic representation of `GL_(r+1)(F)` with a nonzero `GL_(r+1)(O)`-fixed vector,
  when `ψ` has conductor `O`.
- (B) `UnramifiedPairIntegralStatement`: for unramified generic constituents `π` of
  `GL_(n+k+2)(F)` and `σ` of `GL_(n+1)(F)`, Jacquet's normalizations, nonzero functionals
  and normalized spherical tests `w`, `w'`, there is `c` such that for every `s` with
  `c < Re s`, the actual unequal-rank integral (rectangular variable of dimension zero
  with the unit point mass) converges absolutely and equals
  `unramifiedEulerFactor q a a' s = (∏_i ∏_j (1 - a_i a'_j q^(-s)))⁻¹`, with
  `a = unramifiedClass F χ` and `a' = unramifiedClass F χ'`.
- (C) `UnramifiedUnitaryPoleFreeStatement`: for unitarizable such pairs the Euler factor
  has no pole in `Re s ≥ 1`.

No hypothesis is added.

## Source

Jacquet–Shalika, *On Euler products and the classification of automorphic forms II*,
Amer. J. Math. 103 (1981), §1.3–§1.5, printed pp. 780–782 (literature id
`jacquet-shalika-1981-euler-products-ii`): §1.3 for (A), §1.4 display (3) for (B), and
Proposition 1.5(iii) for (C).

## Proof

(A) is the published `Langlands.RankinSelberg.unramifiedSphericalVector` and (C) is the
published `Langlands.RankinSelberg.unramifiedUnitaryPoleFree`. This module proves (B) as
`unramifiedPairIntegral` and assembles the three.

- `norm_natCast_cpow_neg_lt`: for `q > 1` and `r > 0`, every `s` with
  `-log r / log q < Re s` has `‖q^(-s)‖ = q^(-Re s) < r`. This uses
  `Complex.norm_natCast_cpow_of_pos`, and `q^(-Re s) = exp(-Re s · log q)`, which is
  less than `exp(log r)`.
- `unramifiedPairIntegral`:
  1. Jacquet's normalization identifies `q` with the residue cardinality, so `q > 1`.
  2. Worker 1767's `exists_schurCauchy_radius` (module `SchurCauchyEvaluation`, the
     reviewed candidate 42a3c57c-b573-47a8-84e9-4421690538ff, carried here unchanged),
     applied to the two Langlands classes, gives `r > 0` such that for `‖t‖ < r` the Schur pair terms over antitone natural
     tuples are absolutely summable, with sum `(∏_j ∏_i (1 - a_i a'_j t))⁻¹`.
  3. Take `c = -log r / log q`. For `c < Re s`, `t = q^(-s)` satisfies `‖t‖ < r`.
  4. `UnramifiedPairTorus.pairIntegral_eq_tsum` (module
     `UnramifiedPairTorusCoefficient`) turns that summability into absolute convergence
     of the actual integral, with value the same partition sum.
  5. `Finset.prod_comm` exchanges the order of the finite products, which gives
     `unramifiedEulerFactor q a a' s`.
- `unramifiedPair := ⟨unramifiedSphericalVector, unramifiedPairIntegral,
  unramifiedUnitaryPoleFree⟩`.
