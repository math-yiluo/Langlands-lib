# One affine chart for all rational points lifting over a Galois extension

Author: Worker 105.

Helper module for the second countability of rational points
(`EtaleChartSecondCountable`), used for Conrad's p.17 claims
(`Langlands.Global.AdelicSpacePointTopologyStatement`).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.UniformGaloisChart`.

- `exists_chart`: the setting is as follows.
  - `X` is a separated algebraic space over a field `k`.
  - `a : h_V → X` is an étale chart from an affine scheme `V`, separated over `k`.
  - `K/k` is a finite Galois extension.

  Then there is one affine scheme `M` with an étale map `tM : h_M → X` with the following
  property. Let `x̂` be a `k`-point of `X`, and let `v : Spec K → V` lift it, i.e.
  `h(v) ≫ a = h(π) ≫ x̂`. Then some Galois-invariant `K`-point `w` of `M` satisfies
  `h(w) ≫ tM = h(π) ≫ x̂`.

## Proof

This is the construction of `RationalPointEtaleLiftProof.exists_invariant_chart_point`, made
uniform in the point.

1. The `Gal(K/k)`-fold fibre power `Y` of `a` is affine (`exists_of_finite_affine`), so
   `Z = Y ×_k Spec K` is affine. The group acts on `Z` by permuting factors and by the Galois
   action on `Spec K`. The action is free (`prod_isFree`). The map
   `t = h(Z → Y → V) ≫ a` is étale and invariant.
2. `OverAction.exists_quotient_chart`, applied to the stable open `⊤`, gives the affine
   quotient `M` with `q : Z → M` and `tM`. These do not depend on any point.
3. For a lift `v`, the Galois translates of `v` define `y₀ : Spec K → Y`. The point
   `z = (y₀, id)` is equivariant, so `w = z ≫ q` is invariant. Moreover
   `h(w) ≫ tM = h(z) ≫ t = h(π) ≫ x̂`.
