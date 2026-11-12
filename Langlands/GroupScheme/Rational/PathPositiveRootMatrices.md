# Positive-root matrices on normalized path lines

This internal prerequisite derives the matrix of an arbitrary supplied parametrization of a positive path root from the published divided-power weight shifts in `PathRootActions`, the normalized vectors from `PathReflectionScalars`, and the basis and rational coordinate interfaces in `PathNormalizedMatrices` and `PathRootMatrices`.

Work over an arbitrary field `k : Type u`, an actual affine group scheme with a supplied split pinning, a finite decidable representation index `d : Type`, and a highest-weight representation whose highest weight is fundamental at the first vertex of a supplied path component. Fix normalized simple-root parametrizations and a nonzero initial weight vector. For indices `i < l` in `Fin (L + 1)`, let `z` be any root parametrization whose root is `pathWeight i - pathWeight l`.

`pathRootScalar` is the coordinate at `i`, in the normalized path basis, of the first divided power for `z` applied to the vector at `l`. It belongs to `k`. The target weight space has dimension one, so `pathRoot_dividedPower_normalizedPathVector` identifies this divided power with that scalar times the vector at `i`: the proof extracts a scalar from the one-dimensional space and recovers it by the basis-coordinate map.

All divided powers of degree at least two vanish. The first divided power vanishes on every other path vector. Substituting these facts in the exact rational-coordinate formula proves `rationalPathRoot_normalizedPathVector`: the vector at `l` gains `c * pathRootScalar` times the vector at `i`, and all other path vectors are fixed. Taking basis coordinates proves `normalizedPathMatrix_pathRoot`, with matrix

```text
1 + single i l (c * pathRootScalar).
```

This pair establishes neither nonvanishing of the scalar nor formulas for merged reflection representatives, modified products, characteristic polynomials, or the canonical class-quotient cross-section.
