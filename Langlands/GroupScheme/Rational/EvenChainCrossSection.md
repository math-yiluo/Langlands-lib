# The split even-path cross-section of the canonical class quotient

This module proves `Langlands.GroupScheme.SplitEvenChainCrossSectionStatement` as the theorem
`Langlands.GroupScheme.splitEvenChainCrossSection`. The statement covers the setting of
Steinberg 1965, Regular elements of semi-simple algebraic groups, §9.11–9.19, for the actual
canonical quotient. Let `G` be a simply connected group over an arbitrary field `k` with a split
pinning `p`. Fix normalized simple root maps `x`, even-path data `C : p.EvenChainData J`, and
orderings `o : Fin r ≃ J` and `e : Fin q ≃ C.Rest`, with `e` middle-out. Then every rational point
`w` of `ClassFunctions.quotient G` is `g ≫ ClassFunctions.rho G` for exactly one pattern product `g`
in `C.patternSet x (canonicalSimpleReflectionRepresentatives x) o e`.

The proof does not use the middle-out hypothesis: the formulas for the characteristic polynomials
used below hold for every ordering of the factors. It also follows a different route from Steinberg's. The
pattern products are compared with ordinary Steinberg products through characteristic polynomials
on the fundamental representations at the path ends. The comparison is made after extension to
an algebraic closure, and the result comes back to `k` by descent of quotient equalities.

**Sources.** The statement is Steinberg's Corollary 9.19, with Theorem 7.9 for components without
merged pairs (Steinberg 1965, printed pp. 68 and 74–77), in rational-point form over an arbitrary
field. Theorem 7.9 enters through the Library's `splitSteinbergQuotient`, used by
`bijective_steinbergClassMap`. The constructions and comparisons below are internal to this
project; they are not transcriptions of Steinberg's argument.

## Imports

- `EvenChainCrossCoordinates`: the cross-section coordinates `crossFun` and their properties.
- `SteinbergRationalBijection`:
  - `steinbergClassMap` and `bijective_steinbergClassMap`, Steinberg's cross-section on rational
    points (from the Library's `splitSteinbergQuotient`);
  - ascent of quotient equalities;
  - equality of characteristic polynomials from equal quotient images;
  - a nonzero highest-weight vector of a fundamental representation.
- `EvenChainCrossSectionStatement`: the target statement.
- `SimplyConnected.SimplyConnectedFieldExtensionProof`: `isSimplyConnectedFieldExtension`.

These modules import, among others:

- `EvenChainPathCharpoly`, with `charpoly_patternProduct` and `charpoly_rootFactorProduct`;
- the Library modules `EvenChainFieldBaseChange` (base change of the even-path data and
  descent of quotient equalities) and `EvenChainClassGenerators` (the detection criterion
  `EvenChainData.rho_eq_of_charpoly_eq_of_trace_eq`).

## Base change (namespace `Langlands.GroupScheme.SplitPinning`)

Throughout, `F` is an algebraic field extension of `k`. A local instance gives the affine
structure morphism of the base change `G_F`, as in `EvenChainFieldBaseChange`.

- `baseChangeBasePoint_rationalProduct E x cf`: the extension to `F` of the ordinary product
  `∏_j x_(E j)(cf j) n_(E j)` (canonical representatives) is the ordinary product over `F` along
  `fieldBaseChangeOrder E`, with root maps `fieldBaseChangeRootMaps x` and coordinates
  `algebraMap k F ∘ cf`. Proof: combine `steinbergProductPoint_rational` over `k` and over `F`
  with the Library's `baseChangeBasePoint_steinbergProductPoint`.
- `EvenChainData.restCoord_fieldBaseChange e z c v`: the unmerged coordinates of the extended data
  `C.fieldBaseChange` are the images of the original ones. Here the ordering is
  `e.trans C.restFieldBaseChange` and the coordinates are `algebraMap k F ∘ z`.
- `EvenChainData.patCoord_eq_of_rho_eq x o e E c hm Fr hAB ε s t z cf h v hv`: suppose
  `C.half c = m + 1` and `Fr` is a fundamental representation of `p.baseChange` at the end vertex
  of the extended path `c`. Let `A'`, `B'` describe the characteristic polynomials of the extended
  pattern products on `Fr` as in `charpoly_patternProduct` (`hAB`). Suppose also that over `k`
  the pattern product with coordinates `(ε, s, t, z)` has the same quotient image as the ordinary
  product along `E` with coordinates `cf` (`h`). Then for every `v < 2 * C.half c`:
  `patCoord m (algebraMap ∘ C.restCoord e z c) (crossSigma A' (ε c) s_F t_F) (crossDelta B' (ε c) t_F) v = algebraMap k F (cf (E⁻¹ (C.path c v)))`.
  Here `s_F` and `t_F` are the images of `s c` and `t c`.

  Proof: ascend `h` to `F` (`baseChangeBasePoint_rho_eq_of_rho_eq`) and rewrite both points by
  base change. Equal quotient images give equal characteristic polynomials on `Fr`
  (`charpoly_rationalMatrix_eq_of_rho_eq`). Then `patCoord_eq_of_charpoly_eq` of
  `EvenChainCrossCoordinates` applies to the extended data.

## Cross-section constants

`EvenChainData.exists_crossConstants F hG x o e`, for `F` algebraically closed and algebraic over
`k`. There are `A B : J → k`, nowhere zero, such that for all pattern coordinates
`(ε, s, t, z)`:
`patternProduct o e ε s t z ≫ rho G = steinbergClassMap (C.mergedFirstOrder e) x n (crossFun e A B ε s t z ∘ C.mergedFirstOrder e)`.
Here `n` denotes the canonical representatives.

Proof.

1. **Choice of `A` and `B`.** By `bijective_steinbergClassMap`, choose for each `b : Bool` and
   `s₀ : k` coordinates `gam b s₀` of an ordinary product along `E := mergedFirstOrder e`. Its
   quotient image is that of the pattern product with constant pattern `b`, constant `s = s₀`,
   `t = 1` and `z = 0`. Let `a_c = C.path c (half c - 1)` and `b_c = C.path c (half c)`. Define
   - `A c = gam false 0 (E⁻¹ a_c) - gam false 1 (E⁻¹ a_c)`;
   - `B c = gam true 0 (E⁻¹ b_c) - gam false 0 (E⁻¹ b_c)`.
2. **The constants over `F`.** `G_F` is simply connected (`isSimplyConnectedFieldExtension`).
   Let `Fr` be a fundamental representation at the end of the extended path `c`, and let `A'`, `B'`
   be constants as in `charpoly_patternProduct`. Then `A' = algebraMap (A c)` and
   `B' = algebraMap (B c)`.

   Proof: apply `patCoord_eq_of_rho_eq` to the three products `gam false 0`, `gam false 1` and
   `gam true 0`, at the vertices `m = half c - 1` and `m + 1`. By `patCoord_self` the coordinate
   `m` is a common value plus `crossSigma`. That is `0` for `s₀ = 0` and `-A'` for `s₀ = 1`. By
   `patCoord_succ_self` the coordinate `m + 1` is a common value plus `crossDelta`. That is `B'` for
   the pattern `true` and `0` for the pattern `false`.
3. **Nonvanishing.** `splitFundamentalRepresentationsExist` over `F` provides such an `Fr`, and
   `charpoly_patternProduct` provides `A' ≠ 0` and `B' ≠ 0`. Hence `A c ≠ 0` and `B c ≠ 0`.
4. **The identity.** By the Library descent `rho_eq_of_baseChangeBasePoint_rho_eq` it suffices to
   compare the extended points over `F`. These are the extended pattern product and the ordinary
   product along `fieldBaseChangeOrder E`. The Library criterion
   `EvenChainData.rho_eq_of_charpoly_eq_of_trace_eq` for `C.fieldBaseChange` (with `F`
   algebraically closed and `G_F` simply connected) reduces this to two checks.
   - **Path ends.** On a fundamental representation `Fr` at the end of a path `c`, both
     characteristic polynomials are `ordPoly (half c - 1)` of explicit coordinates:
     `charpoly_patternProduct` with the constants of step 2 for the pattern product, and
     `charpoly_rootFactorProduct` for the ordinary product. By `crossFun_path`, `pathCoord`,
     `patCoord_map` and `restCoord_fieldBaseChange` the coordinates agree, so `ordPoly_congr`
     applies.
   - **Off the paths.** On a fundamental representation at a simple root `a` off all paths, the
     highest weight vanishes on every path coroot (`IsFundamentalWeight`). By
     `rationalMatrix_patternProduct_eq_of_offPath` the two matrices are equal; the hypotheses
     about `mergedFirstOrder` come from `exists_path_eq_mergedFirstOrder_castAdd`,
     `mergedFirstOrder_natAdd` and `crossFun_of_offPath`. Their traces therefore agree.

## The theorem

`splitEvenChainCrossSection : SplitEvenChainCrossSectionStatement`. Take the data of the
statement, and `A`, `B` from `exists_crossConstants` with `F = AlgebraicClosure k`. Let
`Φ = steinbergClassMap (C.mergedFirstOrder e) x n`, a bijection.

- **Existence.** Write `w = Φ cv`. By `exists_crossFun_eq` (with `A`, `B` nonzero) there are
  `(ε, s, t, z)` whose cross-section coordinates are `cv ∘ (mergedFirstOrder e)⁻¹`. Then the
  pattern product with these coordinates maps to `Φ cv = w`.
- **Uniqueness.** Suppose two pattern products both map to `w`. Then `Φ` takes the same value at
  their cross-section coordinates (composed with `mergedFirstOrder e`). By injectivity of `Φ`
  these coordinates are equal. `eq_of_crossFun_eq` then gives equal patterns, `s` and `z`, and
  equal `t` on the paths with pattern value `true`. `patternProduct_congr` shows that the two
  pattern products are equal.

The theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
