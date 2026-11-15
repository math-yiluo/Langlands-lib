# Absolute convergence of the partial pair Euler products

Module `Langlands.Global.RankinSelberg.PartialEulerProductConvergence`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Content

Let `F` be a number field with compact adele quotient, `T`, `T'` actual cuspidal
realizations of `GL_(r+1)` and `GL_(t+1)` (`CuspidalOperatorRealization F r` and
`F t`), `P`, `P'` spectral presentations of them, and `S` a finite set of finite places
containing both exceptional sets. For a finite place `v ∉ S`, the Library's
`CuspidalPairBoundaryNonvanishing.partialEulerFactor P P' hP hP' v s` is the unramified pair
factor `L(s, Π_v × Π'_v) = ∏_(i,j) (1 - a_i b_j q_v^(-s))⁻¹`, built from the Satake spectra
`a`, `b` that the two presentations supply at `v`.

- `exists_hasSatakeBound_presentation T P : ∃ C, HasSatakeBound P C`. Every spectral
  presentation of an actual cuspidal realization has a uniform Satake bound
  `‖α‖ ≤ q_v ^ C` for all Satake parameters `α` at all places outside its exceptional set.
- `partialEulerProduct P P' hP hP' s := ∏' v, partialEulerFactor P P' hP hP' v s` is the
  unconditional infinite product (`tprod`) over the subtype `{v // v ∉ S}` of finite places.
  As with every `tprod`, its value is `1` when the family is not multipliable. The theorem
  below shows that the family is multipliable on a right half-plane.
- `exists_partialEulerFactor_convergence P P' hP hP'`: there is `σ` such that for every
  `s` with `σ < Re s`, the family `‖L(s, Π_v × Π'_v) - 1‖` is summable and
  `HasProd (fun v => L(s, Π_v × Π'_v)) (partialEulerProduct P P' hP hP' s)`.

The second conclusion is exactly the convergence conjunct of the Library target
`UnequalEulerFactorizationStatement` (with `p` the value `partialEulerProduct`). The
convergence is uniform over all choices of `x`, `x'`, because the factors depend only on
`P`, `P'` and `S`.

## Provenance

This is internal supporting material for the proof of `UnequalEulerFactorizationStatement`
(Cogdell 2004, §2.2, p.206, with Theorem 3.3, p.215). The standard argument goes back to
Jacquet–Shalika: a uniform bound on the Satake parameters (Jacquet–Shalika 1981, "On Euler
products and the classification of automorphic representations I", via the bound
`|α| < q_v^(1/2)` for unitary generic representations) together with the convergence of
`∑_v q_v^(-σ)` for `σ > 1`. Here the bound is any fixed power `q_v^C`, which is enough for
convergence on some right half-plane and needs no unitarity hypothesis.

`partialEulerProduct` is a derived definition with no separate literature source: it names
the value of the product `∏_(v ∉ S) L(s, Π_v × Π'_v)`.

## Proof

- `exists_hasSatakeBound_presentation`. The published theorem
  `Automorphic.OperatorRealization.irreducibleCentralCharacter`, applied to the irreducible
  realization underlying `T`, gives a Hecke character `ω` with `hω : T.HasCentralCharacter ω`
  (the uniqueness part is not used).
  The published reduction `CuspidalSatakeBound.exists_hasSatakeBound T ω hω P` then gives
  the Satake bound for the presentation `P`.
- `exists_partialEulerFactor_convergence`. Take bounds `A` for `P` and `B` for `P'`, and
  put `σ = A + B + ((r+1)(t+1) + 1)`. Extend the factors to all finite places by the
  polynomial `L v`: `1` for `v ∈ S`, and `pairEulerPolynomial a_v b_v` otherwise. The
  published lemma `CuspidalPairEulerConvergence.summable_norm_inv_eval_sub_one`, which
  compares with `∑_v N(v)^(-(Re s - A - B))`, gives summability of
  `‖(L v)(q_v^(-s))⁻¹ - 1‖` over all finite places. Restricting to the subtype
  `{v // v ∉ S}` (`Summable.subtype`) and unfolding `partialEulerFactor` gives the first
  conclusion. Then `CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one` turns
  summability of `‖f v - 1‖` into `HasProd f (∏' v, f v)`, which is the second conclusion.
