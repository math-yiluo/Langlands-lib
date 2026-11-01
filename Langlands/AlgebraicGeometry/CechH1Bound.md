# Products of independent degree-one classes and the bound for `H¹`

Author: Worker 274.

This module proves the Čech-level core of the dimension bound for `H¹(A, 𝒪_A)`: for a scheme
`X` over a field `k` with a multiplication having a two-sided unit, the Čech product of cocycles
representing `N + 1` linearly independent classes of `H¹(X, 𝒪_X)` is not a Čech coboundary;
hence `H¹(X, 𝒪_X)` has dimension at most `g` if the Čech complex is exact in degree `g + 1`. It
is a helper for the proof of `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`.
It contains no `sorry` and no new axioms.

## Provenance

The argument is the exterior-algebra argument for the dimension of `H¹` of an abelian variety:
degree-one classes are primitive, so the product of `n` independent classes is nonzero, and
cohomology vanishes above the dimension. The registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, (6.12)–(6.15), printed pp. 92–94,
obtains the bound from the Hopf-algebra structure of cohomology (Borel–Hopf over a perfect
field). The implemented route avoids Borel–Hopf and base change: it detects a product of
independent classes with an explicit functional in the Künneth direction
(`Cech.KunnethDetectionStatement`) and works over any field. The exact statements are a
project choice.

## Results

All declarations are in namespace `Langlands.Cohomology.Cech`.

- `isAffineOpen_inter`: if intersections of two affine opens of `X` are affine and every `U i` is
  affine, every finite intersection `inter U σ` is affine.
- `inter_prodCover`: `inter (prodCover p₁ p₂ U V) τ =
  prodOpen p₁ p₂ (inter U (Prod.fst ∘ τ)) (inter V (Prod.snd ∘ τ))`.
- `isAffineOpen_inter_prodCover`: for a fibre product over `Spec R`, finite intersections of the
  product cover are affine if those of `U` and `V` are.
- `exists_functional`: for `X` over `Spec k` (`k` a field), a finite family `U` covering `X` and
  a `k`-linear functional `μ` on `H¹(X, 𝒪_X)`, there is a `k`-linear functional `l` on Čech
  `1`-cochains (with the `k`-module structure given by `secHom`) that kills coboundaries and
  satisfies `l z = μ x` whenever the cocycle `z` represents `x` (`CechTheta.Rep`). The map
  cocycles `→ H¹` is `k`-linear by `CechTheta.rep_add`, `CechTheta.rep_smul` and
  `CechTheta.rep_unique`; `l` extends `μ` composed with it (`LinearMap.exists_extend`).
- `exists_dual`: for a linearly independent family `x : Fin (n + 1) → M`, there is a functional
  `μ` with `μ (x 0) = 1` and `μ (x (r + 1)) = 0`.
- `not_exists_prod_eq_d`: assume `Cech.KunnethDetectionStatement`. Let `X` be a scheme over
  `Spec k` with all global functions constant, `P` the fibre product with projections `p₁`, `p₂`,
  `m : P ⟶ X`, `e` a `k`-point and axes `i₁`, `i₂` as in `Cech.exists_pull_sub_refine_eq_d`, and
  `U` a finite cover by affine opens with affine finite intersections. If cocycles `z r`
  represent linearly independent classes `x r` (`r : Fin (N + 1)`), then
  `Cech.prod (N + 1) z` is not a Čech coboundary. Proof by induction on `N`: for `N = 0` a
  coboundary represents `0`. In the step, a coboundary `prod z = d c` pulls back along `m` to a
  coboundary on `primCover`; by primitivity and `prod_sub_eq_d`, the refinement of
  `prod (p₁^* z + p₂^* z)` is a coboundary there; by refinement injectivity
  (`CechShift.exists_d_eq_of_refine`) `prod (p₁^* z + p₂^* z)` is a coboundary on the product
  cover; Künneth detection with the functional `l` built from `μ` (`exists_dual`,
  `exists_functional`) makes `prod (Fin.tail z)` a coboundary, contradicting the induction
  hypothesis for the independent classes `x 1, …, x (N + 1)`.
- `finiteDimensional_and_finrank_le`: under the same hypotheses, if moreover
  `Cech.ExactAt (ab X.presheaf) U g` (every Čech `(g + 1)`-cocycle of `𝒪_X` for `U` is a
  coboundary), then `H¹(X, 𝒪_X) = (relativeCohomology πX 1).obj (SheafOfModules.unit _)` is
  finite-dimensional over `k` with `finrank ≤ g`. Every linearly independent finite set has at
  most `g` elements: otherwise `g + 1` of its members are represented by cocycles
  (`CechTheta.exists_cocycle_rep`), their product is a cocycle in degree `g + 1`, hence a
  coboundary, contradicting `not_exists_prod_eq_d`. Then `rank_le`,
  `Module.rank_lt_aleph0_iff` and `Module.finrank_le_of_rank_le` conclude.
