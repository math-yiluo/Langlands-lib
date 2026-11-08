# Canonical reflection representatives on consecutive path lines

This module is an internal prerequisite for the even type `A` case of the
quasi-split Steinberg quotient task (Steinberg 1965, §9.10–9.19). Steinberg
computes in the standard representation of `SL_{2m+1}`. There a simple root
element is an elementary matrix `1 + t E_{i,i+1}`, and the Weyl representative
of a simple reflection sends `e_{i+1} ↦ e_i` and `e_i ↦ -e_{i+1}`. This module
obtains the same normal form intrinsically, for the highest-weight
representation of `Rational.PathFundamentalWeights` at the fundamental weight
of the end of a path component `β` of type `A_L`. It determines how the
canonical reflection representative of each path vertex acts on the two lines it
moves. Hence the first divided power of the normalized root map is an
isomorphism between consecutive lines. It then builds a normalized family of
path vectors in which the canonical representatives act as above.

## Setting

The additive-group lemmas are in
`Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers`, for an actual
matrix representation `σ` of the one-dimensional vector group over an arbitrary
field `k`. The remaining results are in `Langlands.GroupScheme.SplitPinning`, for a
supplied split pinning `p` of an actual affine group scheme `G`. There `ρ` is an
actual `MatrixRepresentation G d`, `hρ : p.IsHighestWeight ρ lam`,
`hβ : IsPathComponent β` and `hlam : IsPathFundamental β lam`. `V_j` denotes the
line `p.representationWeightSpace ρ (pathWeight β lam j)`. For a path vertex
`β i` (`i < L`) and a normalized root map `x` of its root, `B` is
`dividedPower (ρ.restrict x.hom) 1`, and `n` is the published canonical
representative `x.reflectionRepresentative` (`Rational.SteinbergCanonicalRepresentatives`).

## Results

- `exists_rationalMatrix_eq_one_add`: if the divided powers of `σ` of degree at
  least two vanish, every rational point of the vector group has matrix
  `1 + c A₁` for some `c ∈ k`. `rationalMatrix_scalarPoint_one` gives
  `1 + A₁` for the point with coordinate one, and `one_add_smul_mulVec` gives
  the action `v ↦ v + c • D₁ v`.
- `exists_rationalMatrix_eq_one_add_of_isRepresentedBy`: the same for rational
  points of a subgroup represented by an additive map.
- `NormalizedRootParametrization.rationalMatrix_unitPoint`: the normalized root
  point at coordinate one (`unitPoint`) has matrix `1 + A₁`.
- `canonicalReflection_mulVec_of_mem_succ`: for `w ∈ V_{i+1}`, `n w = B w`.
- `dividedPower_one_injective_succ`: `B` is injective on `V_{i+1}`.
- `canonicalReflection_mulVec_of_mem`: for `v ∈ V_i`, `n v ∈ V_{i+1}` and
  `B (n v) = -v`.
- `NormalizedRootParametrization.isTorusEquivariant_path`: the normalized root
  map of `β i` is equivariant for `ε_i - ε_{i+1}`.
- `pathSuccEquiv` (definition): `B` as a linear isomorphism `V_{i+1} ≃ₗ[k] V_i`,
  with `pathSuccEquiv_apply`.
- `normalizedPathVector` (definition): given a family `x` of normalized
  simple-root maps and `v₀ ∈ V_0`, the vectors `v j ∈ V_j` with `v 0 = v₀` and
  `v (j + 1)` the preimage of `v j` under `pathSuccEquiv` for `β j`. It is `0`
  past the end of the path.
- `dividedPower_normalizedPathVector_succ`: `B (v (i + 1)) = v i`. Combined with
  `PathRootActions` (the root map acts as `1 + c A₁` and `A₁` kills the other
  lines), the root map of `β i` acts as `1 + t E_{i,i+1}` on the vectors `v j`.
- `normalizedPathVector_ne_zero`: if `v₀ ≠ 0`, every `v j` with `j ≤ L` is
  nonzero.
- `canonicalReflection_normalizedPathVector_succ` and
  `canonicalReflection_normalizedPathVector_self`: the canonical representative
  of `β i` sends `v (i + 1)` to `v i` and `v i` to `-v (i + 1)`.

## Proof as implemented

**Rational matrices.** For a rational point `g = scalarPoint c` of the vector
group, its constant point over `Spec k` is the affine point with the
corresponding coordinate `c'`. The published `affineMatrix_constantPoint`
identifies the affine matrix with the rational matrix, and
`PathRootActions.affineMatrix_eq_one_add` gives `1 + c' A₁`. For the coordinate
one, `c'` is the image of `1` under ring homomorphisms, hence `1`.

**The representative.** The canonical representative is
`y₁ · x(1) · y₂`, where `y₁` and `y₂` form the published opposite pair and lie in the
rational root subgroup of `-α`. That subgroup is represented by the negative map
of the published `SplitPinning.nonempty_linkedRootParametrization`. That map is
equivariant for `ε_{i+1} - ε_i`. Write `C` for its first divided power. By
`PathRootActions`, `B` and `C` have vanishing higher divided powers. `B` maps
`V_{i+1}` into `V_i` and kills `V_i`, while `C` maps `V_i` into `V_{i+1}` and
kills `V_{i+1}`. So `n` acts as `(1 + c₁ C)(1 + B)(1 + c₂ C)`.

For `w ∈ V_{i+1}` this gives `n w = (w + c₁ C B w) + B w`. Here the first summand
lies in `V_{i+1}` and the second in `V_i`. Because `n` normalizes the torus with
the reflection of `β i`, the published normalizer transport gives `n w ∈ V_i`.
Distinct path lines are independent, so the first summand vanishes and
`n w = B w`. Invertibility of the rational matrix then makes `B` injective on
`V_{i+1}`.

For `v ∈ V_i` the same expansion gives
`n v = (v + c₂ B C v) + ((c₁ + c₂) C v + c₁ c₂ C B C v)`, and
`n v ∈ V_{i+1}` forces `v + c₂ B C v = 0`. Applying `B C` to this relation gives
`B C v + c₂ B C B C v = 0`. These two relations show by direct computation
(`module`) that `B (n v) = -v`, without dividing by any scalar.

**The normalized vectors.** `B` is an injective linear map between
one-dimensional spaces (`finrank_pathWeightSpace`), so
`LinearMap.linearEquivOfInjective` makes it an isomorphism. The vectors are
defined by structural recursion. The two representative formulas follow from
the results above and from injectivity of `B` on `V_{i+1}`, applied to
`n (v i) + v (i + 1)`.

## Scope

The module treats only the simple path vertices and their canonical
representatives. It does not treat the merged root of Steinberg's `N''` and
`N'''`, the torus factor, or products. It computes no characteristic
polynomial on `N'''` and proves no isomorphism onto a stratum. These remain
obligations of the host task.
