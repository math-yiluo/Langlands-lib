# Galois-stable even-path data from Galois-compatible merged data

Provenance: internal derived result. This module proves the conclusion of
`EvenChainGaloisDataStatement` for pairing-compatible pinning data, assuming
one explicit input: merged-root data at the pairs, transported exactly by the
Galois action (`MergedGaloisData`). A separate module
(`MergedRootGaloisData`) constructs that input. The present module supplies the
paths, the orderings and the Galois transport of the pattern products. The
target is a derived finite-Galois, rational-point formulation of results of
Robert Steinberg, *Regular elements of semi-simple algebraic groups*, Publ.
Math. IHÉS 25 (1965), 49–80 (source
`steinberg-1965-regular-elements-semisimple-groups`): 9.3 (printed p.72), 9.4
(printed pp.72–73), the notation before 9.11 and 9.11 (printed p.74), and the
proof of 9.7 e) in the last paragraph of printed p.77. The Markdown of the
target `EvenChainGaloisDataStatement` gives the full source account. The
treatment of the unmerged simple roots by Galois orbits follows 9.4. The
middle-pair factors follow the notation before 9.11 and the last paragraph of
p.77. Steinberg reduces to one component; this module treats all components
at once, using the commutation of blocks of distinct paths.

Throughout, `k, K : Type u` are fields with `Algebra k K`, `G` is an affine group
scheme over `Spec k`, and `D : PairingCompatiblePinningData k K G`. No
finiteness or Galoisness of `K/k` is assumed in this module. Rational points
are those of the base change `GaloisPointComparison.baseChanged k K G`, and
`σ ↦ rationalConjugate σ` is the Galois action on them.

## Definitions

- `D.Pairs`: the index type `PairIndex D.action` of `RootDatumPairedPaths`.
  It consists of the simple roots `c.1` that have a distinct non-orthogonal
  simple root, the partner, in their Galois orbit, each pair represented once.
  It carries the action `pairAction D.isPairingCompatible`.
- `D.MergedGaloisData`: a structure with
  - `data : D.Pairs → D.pinning.SteinbergModifiedData`;
  - `a_eq`, `b_eq`: the merged simple roots of `c` are `c.1` and
    `partner D.action c.1`;
  - `ca_eq`, `cb_eq`: both unipotent coordinates are `1`;
  - `nAlpha_mem`: the merged representative lies in `U(α)(K) ⊔ U(-α)(K)`;
  - `xAlpha_conj`: `σ(x_α^c(s)) = x_α^{σ c}(σ s)`;
  - `nAlpha_conj`: `σ(n_α^c) = n_α^{σ c}`;
  - `coroot_conj`: `σ(α_c^∨(t)) = α_{σ c}^∨(σ t)`, with the unit `t` mapped by
    `Units.map σ`.
- `MD.evenChainData`: the `D.pinning.EvenChainData D.Pairs` with the paths
  `path D.isPairingCompatible`, their lengths `2 * half`, the published
  path-component and disjointness proofs, and `modified := MD.data`.
- `MD.restAction`: the Galois action on the unmerged simple roots `Rest`, by
  restricting `D.action`.
- `MD.restKey z`: the level `level D.isPairingCompatible z.1`, the distance of
  `z` from the middle pair of its path.
- `MD.restBlocks` and `MD.restOrdering`: the Galois orbit blocks of `Rest`
  sorted by `restKey` (`sortedBlocks`), and the enumeration of `Rest` listing
  them in that order (`sortedOrdering`).

## Statements

- `smul_orientation`: for a pair `c` and `σ`, either `(σ • c).1 = σ c.1` and the
  partner of `(σ • c).1` is `σ (partner c.1)`, or the two roots are exchanged.
- `MergedGaloisData.evenChainData_modified`, `mem_rest_iff`: a simple root is
  unmerged iff it is not paired. `restSMul_val`, `restKey_smul`: the action on
  `Rest` and invariance of the key.
- `isMiddleOut`: `MD.restOrdering` is middle-out for `MD.evenChainData`.
- `ua_eq`, `ub_eq`: `u_a = x_{c.1}(1)` and `u_b = x_{partner c.1}(1)` for the
  normalized root maps `D.rootMaps`.
- `conj_simple`: `σ(x_z(1)) = x_{σ z}(1)` for simple roots `z`.
- `block_true`, `block_false`: the two forms of the blocks.
- `block_rationalConjugate`: for each pair `c`, pattern value `ε`, coordinate
  `s` and unit `t`, there is `s'` such that the conjugate of the block
  `block c ε s t` is `block (σ • c) ε s' (σ t)`.
- `blocks_rationalConjugate`: for every enumeration `o : Fin r ≃ D.Pairs`, the
  conjugate of the ordered product of blocks with data `ε, s, t` is the ordered
  product, in the same order `o`, of blocks with the pattern `ε (σ⁻¹ • ·)`, the
  units `σ (t (σ⁻¹ • ·))` and suitable coordinates `s'`.
- `restBlocks_pairwise`: two entries of a sorted block of `Rest` are distinct
  and orthogonal.
- `rest_rationalConjugate`: the conjugate of the ordered product of the
  unmerged factors `x_{e j}(d j) n_{e j}` along `e = MD.restOrdering` is the
  product in the same order with coordinates `σ (d (e⁻¹ (σ⁻¹ • e j)))`.
- `patternSet_stable`: for every enumeration `o` of the pairs, the set of
  pattern products with the canonical simple-reflection representatives is
  stable under every `rationalConjugate σ`.
- `exists_evenChainGaloisData`: given `MD : D.MergedGaloisData`, there are
  `J`, `Fintype J`, `C : D.pinning.EvenChainData J`, `r, q`, `o : Fin r ≃ J`,
  `e : Fin q ≃ C.Rest` with `C.IsMiddleOut e` and Galois-stable `C.patternSet`.
  This is exactly the conclusion of `EvenChainGaloisDataStatement` for `D`.

## Implemented proof

The paths and their properties come from `RootDatumPairedPaths`. The selected
root of `c` is entry `half - 1` (`path_left`), and its partner is entry `half`
(`path_right`). `mem_rest_iff` is `isPaired_iff_exists`. The restricted action is
well defined because pairedness is invariant (`isPaired_apply_iff`).
`isMiddleOut` follows from `sortedOrdering_lt_of_key_lt`, since `level_path`
identifies the key of `path c i` with `middleDistance (half c) i` and the key is
invariant by `level_apply`.

For a block with pattern `false`, `block_rationalConjugate` uses `xAlpha_conj`
and `nAlpha_conj` with `s' = σ s`. For pattern `true`, it uses
`smul_orientation`. Both unipotent coordinates are `1`, so
`RootMapsGaloisCompatible.rationalPoints` gives `σ(u_a) = x_{σ a}(1)` and
`σ(u_b) = x_{σ b}(1)`. If the orientation is kept, these are `u_a` and `u_b` of `σ • c`,
and again `s' = σ s`. If the orientation is reversed, the conjugate starts with
`u_a' u_b'` instead of `u_b' u_a'`, where `a', b'` are the merged roots of
`σ • c`. Worker 90's `adjacent_rationalPoint_reorder`
(`AdjacentSimpleRootCommutator`) gives `r` with
`x_{a'}(1) x_{b'}(1) = x_{b'}(1) x_{a'}(1) x_α(r)`, because
`⟨a', b'^∨⟩ = ⟨b', a'^∨⟩ = -1` (`pairing_partner`). Additivity
`rationalPoint_add` then absorbs `x_α(r)` into the root coordinate,
with `s' = r + σ s`.

`blocks_rationalConjugate` chooses the coordinates `S` from
`block_rationalConjugate` and writes both sides as images of one function `f`
on pairs: the conjugate is `f` mapped over `σ • o j` and the target is `f`
mapped over `o j`. The two lists of pairs are permutations of each other
(`List.perm_ext_iff_of_nodup`), and blocks of distinct pairs commute
(`EvenChainData.commute_block` from `EvenChainBlockCommutation`), so
`List.Perm.prod_eq'` gives equality of the products.

`rest_rationalConjugate` follows the published orthogonal case
(`EvenChainOrthogonalGaloisData`). It writes the factors as
`D.rationalRootFactor`, splits the product along the sorted blocks
(`sortedBlocks_flatten_eq_ofFn`, `List.prod_flatten`), and transports each
factor by `rationalRootFactor_rationalConjugate`. Within each block the entries
are pairwise distinct and orthogonal: two distinct unpaired roots in one orbit
are orthogonal by `not_isOrthogonal_of_not_isPaired`. So their factors commute
(`commute_rationalRootFactors`), and `sortedBlocks_invariant` with
`List.Perm.prod_eq'` reorders each block. The blocks keep their order.

`patternSet_stable` unfolds a pattern product into the block product and the
unmerged product and rewrites both with the two transport theorems. The
transported pattern, units and coordinates are explicit witnesses.
`exists_evenChainGaloisData` packages `J := D.Pairs` with
`Fintype.ofFinite`, the enumeration `(Finite.equivFin D.Pairs).symm`,
`MD.restOrdering`, `isMiddleOut` and `patternSet_stable`.
