# Cross-section coordinates of even-path pattern products

This module imports `Langlands.GroupScheme.Rational.EvenChainPathCharpoly`. It is an internal
prerequisite of the split even-path cross-section task
(`Langlands.GroupScheme.SplitEvenChainCrossSectionStatement`, Steinberg 1965, Regular elements
of semi-simple algebraic groups, §9.15–9.19).

**Provenance: internal.** Steinberg's §9 proves the cross-section by other means. The
statements below were derived for this project. They reduce the cross-section property of the
pattern products to the rational Steinberg bijection for ordinary products, by matching
characteristic polynomials on path representations. Every result is stated below and proved
in Lean.

## Setting

`k` is a field. `G` is a group scheme over `Spec k` with affine structure morphism and a split
pinning `p`. `C : p.EvenChainData J` is even-path data, as in
`Langlands.GroupScheme.Rational.EvenChainPatternProducts`. For each index `c : J`,
`C.path c : Fin (2 * C.half c) → p.base.support` lists a path component of the Dynkin diagram.
Distinct indices give disjoint paths. The merged simple roots of the path `c` are
`(C.modified c).a = C.path c (half c - 1)` and `(C.modified c).b = C.path c (half c)`.
`C.Rest` is the subtype of unmerged simple roots, and `e : Fin q ≃ C.Rest` is an ordering of
them. `x` is a family of normalized simple root parametrizations. The pattern products
`C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t z` and the
unmerged coordinates `C.restCoord e z c` (from `EvenChainPathCharpoly`) are used with the
canonical reflection representatives. `patCoord`, `ordPoly`, `eq_of_patCoord_eq`,
`exists_patCoord_eq` and `eq_of_ordPoly_eq` are from `Langlands.LinearAlgebra.PathCoxeterCoordinates`.

## Two coordinates of `patCoord`

In the namespace `Langlands.LinearAlgebra.PathCoxeter`, over any commutative ring:

- `patCoord_self m d σ δ δ'`: `patCoord m d σ δ m = patCoord m d 0 δ' m + σ`.
- `patCoord_succ_self m d σ δ`: `patCoord m d σ δ (m + 1) = patCoord m d σ 0 (m + 1) + δ`.

Both follow by unfolding `patCoord` and `patU`.

## Path positions

The remaining results are in the namespace `Langlands.GroupScheme.SplitPinning.EvenChainData`.

- `eq_of_path_eq f h`: if `C.path c' v' = C.path c v`, then `f c' v' = f c v` for every
  `f : (c : J) → ℕ → α`. This holds because the paths are disjoint and each path is injective.
- `half_pos c`: `0 < C.half c`.
- `exists_path_eq_of_not_rest`: a simple root that is not unmerged is a path vertex.
- `rest_of_offPath`: a simple root that is not a vertex of any path is unmerged.

## The ordering with merged roots first

- `Merged` is the subtype of simple roots that are not unmerged, i.e. the two middle vertices
  of the paths. `mergedCount` is its cardinality.
- `mergedFirstOrder e : Fin (C.mergedCount + q) ≃ p.base.support` lists the merged roots
  first, in the order of `Fintype.equivFin`, and then the unmerged roots in the order `e`.
- `mergedFirstOrder_natAdd e j`: `mergedFirstOrder e (Fin.natAdd mergedCount j) = e j`.
- `exists_path_eq_mergedFirstOrder_castAdd e i`: `mergedFirstOrder e (Fin.castAdd q i)` is a
  path vertex.

## Cross-section coordinates

For `A B : k`, `b : Bool`, `s : k` and `t : kˣ`:

- `crossSigma A b s t` is `-(t s A)` if `b = true` and `-(s A)` if `b = false`.
- `crossDelta B b t` is `t B` if `b = true` and `0` if `b = false`.

These are the middle values `σ` and `δ` in `charpoly_patternProduct`. For constants
`A B : J → k` and pattern coordinates `ε : J → Bool`, `s : J → k`, `t : J → kˣ`,
`z : Fin q → k`:

- `pathCoord e A B ε s t z c` is the coordinate sequence
  `patCoord (half c - 1) (restCoord e z c) (crossSigma (A c) (ε c) (s c) (t c)) (crossDelta (B c) (ε c) (t c))`.
- `crossFun e A B ε s t z : p.base.support → k` is defined as follows. At a vertex
  `C.path c v` it is `pathCoord e A B ε s t z c v`. At an unmerged simple root `w` off all paths
  it is `z (e⁻¹ w)`. At any other root it is `0`, a case that does not occur.
- `crossFun_path`: `crossFun e A B ε s t z (C.path c v) = pathCoord e A B ε s t z c v`.
- `crossFun_of_offPath`: if `e j` is not a vertex of any path, then
  `crossFun e A B ε s t z (e j) = z j`.

**Injectivity** (`eq_of_crossFun_eq hA hB h`). Assume `A c ≠ 0` and `B c ≠ 0` for all `c`.
If `crossFun e A B ε s t z = crossFun e A B ε' s' t' z'` pointwise, then
`ε = ε'`, `s = s'`, `t c = t' c` whenever `ε c = true`, and `z = z'`.

Proof: on each path, `eq_of_patCoord_eq` gives equal `δ` and `σ` and equal unmerged
coordinates. `δ` decides the pattern, since `t B ≠ 0`. Then `δ` gives `t` when `ε c = true`,
and `σ` gives `s`. Unmerged coordinates on a path come from `restCoord_eq`, and those off all
paths come from `crossFun_of_offPath`.

**Surjectivity** (`exists_crossFun_eq hA hB cv`). Assume `A c ≠ 0` and `B c ≠ 0` for all `c`.
Then every `cv : p.base.support → k` is `crossFun e A B ε s t z` for some `ε, s, t, z`.

Proof: on each path, `exists_patCoord_eq` gives `d`, `σ` and `δ` with `patCoord` equal to
`cv` along the path. Then:

- `ε c` is `δ ≠ 0`;
- `t c` is `δ / B c` if `δ ≠ 0`, and `1` otherwise;
- `s c` is `-σ / (A c t c)`;
- `z` is `d` at unmerged path vertices and `cv` at unmerged roots off all paths.

The unmerged coordinates agree with `d` on the relevant indices, so `patCoord_congr` applies.

## Pattern products with the same coordinates

`patternProduct_congr o hε hs ht hz`: if `ε = ε'`, `s = s'`, `z = z'` and `t c = t' c`
whenever `ε c = true`, then the pattern products with the canonical representatives agree.
The unit `t c` enters only the blocks with `ε c = true`.

## Representations orthogonal to all paths

`rationalMatrix_patternProduct_eq_of_offPath hρ hlam o E' h1 h2 ε s t z cf hcf`. Here `ρ`
has highest weight `lam`, and `lam` vanishes on all path coroots. `E' : Fin (N + q) ≃ p.base.support`
lists path vertices in its first `N` positions (`h1`) and the unmerged roots `e j` in its last
`q` positions (`h2`). Assume `cf (Fin.natAdd N j) = z j` whenever `e j` is off all paths
(`hcf`). Then `ρ.rationalMatrix` of the pattern product equals `ρ.rationalMatrix` of the
ordinary product `∏_j x_(E' j)(cf j) n_(E' j)` (in increasing order of `j`).

Proof: by the Library's locality lemmas `rationalMatrix_block_eq_one_of_offPath` and
`rationalMatrix_rootFactor_eq_one_of_offPath`, the blocks and all factors at path vertices act
trivially. The remaining factors, at unmerged roots off all paths, agree by `hcf`.

## Coordinates from characteristic polynomials

`patCoord_eq_of_charpoly_eq c hm hρ hlam v₀ hv₀ hAB o E' ε s t z cf h v hv`. Here
`C.half c = m + 1`, `ρ` has highest weight the fundamental weight of the end vertex
`C.path c 0`, and `v₀ ≠ 0` is a vector of the corresponding weight space. `hAB` says that the
constants `A'`, `B'` describe the characteristic polynomials of all pattern products on `ρ`,
in the form of the conclusion of `charpoly_patternProduct`. `h` says that the pattern product
and an ordinary product along an ordering `E' : Fin N ≃ p.base.support` with coordinates `cf`
have the same characteristic polynomial on `ρ`. Then, for every `v < 2 * C.half c`,
`patCoord m (restCoord e z c) (crossSigma A' (ε c) (s c) (t c)) (crossDelta B' (ε c) (t c)) v = cf (E'⁻¹ (C.path c v))`.

Proof: rewrite both characteristic polynomials with `hAB` and `charpoly_rootFactorProduct`, then
compare coefficients by `eq_of_ordPoly_eq`.
