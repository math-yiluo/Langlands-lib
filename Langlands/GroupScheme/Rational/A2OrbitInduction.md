# Galois induction along the pieces of an `A₂` orbit

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.A2OrbitInduction`, namespace
`Langlands.GroupScheme.GaloisCompatiblePinningData`.

## Setting

- `D : GaloisCompatiblePinningData k K G`, and `Γ = Aut_k(K)`.
- `m₀` is a root index of the pinning. `PairOrbit m₀` is its orbit under the Galois action on
  root indices, written `rootIndexAction` (module `Rational.A2OrbitPieces`).
- For `c` in the orbit, `pairElement c` is a chosen `σ` with `σ • m₀ = c`, and `pairA p₀ c`,
  `pairB q₀ c` are the images of `p₀`, `q₀` under `D.action (pairElement c)`.
- `basePair m₀` is `m₀` itself as a point of its orbit.
- `rationalConjugate` is coefficient conjugation on `G(K) = rationalPoints (baseChanged k K G)`.

## Definitions

- `transportElement c = pairElement c * (pairElement (basePair m₀))⁻¹`. It carries the base
  piece to `c` (`transportElement_smul`). It also carries the base orientation to the chosen
  orientation at `c`: `D.action (transportElement c) (pairA p₀ (basePair m₀)) = pairA p₀ c`
  (`action_transportElement_pairA`), and likewise for `pairB`
  (`action_transportElement_pairB`).
- `inducedPoint h₀ c = rationalConjugate (transportElement c) h₀`, the transport of a point
  `h₀ ∈ G(K)` to the piece `c`.

## Results

- `rationalConjugate_inducedPoint hfix σ c`. Assume `hfix`: `h₀` is fixed by every `g` with
  `g • basePair m₀ = basePair m₀`. Then `σ(inducedPoint h₀ c) = inducedPoint h₀ (σ • c)`.
  Proof:
  1. Let `g = (transportElement (σ • c))⁻¹ σ (transportElement c)`. It fixes the base piece.
  2. Then `σ · transportElement c = transportElement (σ • c) · g`.
  3. Conclude by `rationalConjugate_mul` and `hfix g`.
- `rationalConjugate_inducedProduct hfix hcomm σ`. Assume also `hcomm`: transports to distinct
  pieces commute. Then the ordered product
  `∏ₗ inducedPoint h₀ (pieceEquiv m₀ l)` (a `List.ofFn` product over the enumeration
  `pieceEquiv m₀` of the pieces) is fixed by every `σ`. Proof:
  1. `σ` is multiplicative (`map_list_prod`).
  2. By the previous result, `σ` sends the `l`-th factor to the factor at `π l`, where `π` is
     the permutation of `Fin r` induced by `σ` on the orbit.
  3. A product of pairwise commuting factors does not change under permutation:
     `Equiv.Perm.ofFn_comp_perm` and `List.Perm.prod_eq'`.

## Provenance

This is an internal construction, the usual induction from a stabilizer for Galois-fixed
points. It makes no new mathematical assertion.
