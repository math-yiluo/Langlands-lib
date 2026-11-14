# Coroot coordinates, good units and stabilizers for `A₂` orbits

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.A2OrbitGeneration`.

The setting is that of modules `Rational.A2OrbitPieces` and `Rational.A2OrbitDescent`:
- `D : GaloisCompatiblePinningData k K G` with pinning `p`, and `Γ = Aut_k(K)`;
- `t : S ⟶ D.torus`;
- `m₀` is the merged root of two simple roots `p₀ ≠ q₀` with the same restriction `a_K`;
- `PairOrbit m₀` is the Galois orbit of `m₀`, and `M` are merged-root data
  (`exists_mergedPieces`);
- the base piece is `c₀ = basePair m₀`, with base roots `A = pairA p₀ c₀` and
  `B = pairB q₀ c₀`.

The module also uses the accepted modules of Worker 185:
- `Rational.SimpleCorootCoordinates` (`fundamentalWeightEval`, `simpleCorootProduct`);
- `Rational.SimpleCorootGaloisTransport` (`torusPointEquiv`, `torusCoordinates`);
- `Rational.SimpleCorootOrbitDecomposition` (`torusCoordinates_rationalConjugate`).

## General lemmas

- `rationalPoints_map_injective_of_mono f`: rational points of a group-scheme map whose
  underlying scheme map is a monomorphism are injective. Uses `Over.mono_of_mono_left`.
- `SplitPinning.tripleProd_ne_one p hS hline F ha0 hx hz hy hg hzl`. A product of piece triples
  lying in the restricted root group of `a ≠ 0`, with some merged coordinate `z l ≠ 1`, is
  nontrivial. Piece coordinates are unique: compare with the trivial triples using the
  published `PieceFamily.triples_eq_of_tripleProd_eq`, `enum_injective` and `range_enum`.
- `fundamentalWeightEval_action hspan hjc hx σ b`. Suppose the scalar extension of
  `g ∈ G(k)` equals `p.inclusion(x)` for a point `x` of the pinned torus. Then the
  simple-coroot coordinates of `x` are Galois equivariant:
  `fundamentalWeightEval (D.action σ b) x = σ(fundamentalWeightEval b x)`. Proof:
  1. `torusPointEquiv x` and `x` have the same image in `G_K` (`D.inclusion_eq`).
  2. It is Galois-fixed: use `rationalConjugate_map`, `rationalConjugate_rationalExtend`, and
     injectivity of rational points of the closed immersion `(D.inclusion)_K`.
  3. Apply `torusCoordinates_rationalConjugate`.
- `simpleCorootProduct_mul`, `simpleCorootProduct_one`, `simpleCorootProduct_inv`: the
  simple-coroot product is multiplicative in the unit family.

## Good units

- `IsOrbitFamily A c`: `c : simple roots → Kˣ` is Galois equivariant,
  `c(σ b) = σ(c b)`, and equals `1` off the Galois orbit of `A`.
- `orbitGoodUnits t A : Subgroup Kˣ`: the values `c A` of orbit families `c` such that
  `p.inclusion(simpleCorootProduct c)` lies in `relativeRootGeneratedExtension k K i`, the
  image of `G(k)^+`, where `i = groupHom t ≫ D.inclusion`. It is a subgroup by the
  multiplicativity lemmas.
- `IsOrbitFamily.eq`: two orbit families with the same value at `A` are equal, since the
  value at `σ A` is `σ(c A)`.
- `mem_of_mem_orbitGoodUnits hc h`: if `c` is an orbit family and `c A` is a good unit, the
  coroot product of `c` lies in the image of `G(k)^+`.

## Stabilizers

- `rootStabilizer A`: the stabilizer of `A` under `D.action`. `pairStabilizer m₀`: the
  stabilizer of the base piece.
- `pairStabilizer_cases`: an element of the pair stabilizer fixes `A` and `B`, or exchanges
  them (`pair_orient`).
- `mem_pairStabilizer_of_action`: if `g A ∈ {A, B}`, then `g` stabilizes the base piece
  (`pair_eq_of_mem`).
- `rootStabilizer_le_pairStabilizer`.
- `baseA_ne_baseB`: `A ≠ B`.
- `swapElement σ₀ m₀ = π σ₀ π⁻¹` with `π = pairElement c₀`. If `D.action σ₀ p₀ = q₀`, it
  sends `A` to `B` (`action_swapElement`). It lies in the pair stabilizer but not in the root
  stabilizer (`swapElement_mem`, `swapElement_not_mem`).
- `relIndex_rootStabilizer`: the root stabilizer has index `2` in the pair stabilizer. Use
  `Subgroup.index_eq_two_iff` with the swap: an element of the pair stabilizer fixes `A`
  exactly when its product with the swap does not.

## The commutator scalar and fixed base triples

Assume `G_K` smooth where needed.
- `simplePoint_zero`: `x_b(0) = 1`.
- `exists_commutatorScalar`: `x_A(1) x_B(1) = x_B(1) x_A(1) x_m(r)` for some `r ∈ K`, with
  `x_m = (M c₀).xAlpha`. This is the published `adjacent_rationalPoint_reorder`, with the
  pairings of `pair_pairings`.
- `commute_merged_simple s c`: `x_m(s)` commutes with `x_A(c)` and `x_B(c)` (published
  `piece_commute_m_q`, for the piece and for its swap).
- `rationalConjugate_simplePoint`: `σ(x_b(c)) = x_{σ b}(σ c)`
  (`RootMapsGaloisCompatible.rationalPoint`).
- `commutatorScalar_fixed hr hg`: elements of the root stabilizer fix `r`. Conjugate the
  relation by `g`, then cancel and use injectivity of `x_m`.
- `commutatorScalar_swap hr hg hgA`: a swapping element `g` of the pair stabilizer satisfies
  `g r = -r`. Conjugating the relation gives `x_B x_A = x_A x_B x_m(g r)`; the relation itself
  gives `x_B x_A = x_A x_B x_m(r)⁻¹`.
- `pieceTriple_one_fixed hr hw hσA hwr g hg`. Let `w` be fixed by the root stabilizer, and
  let `w - σ w = r` for a swapping element `σ`. Then the base triple
  `x_B(1) x_m(w) x_A(1)` is fixed by the pair stabilizer.
  - A non-swapping element fixes `A`, `B` and `w`.
  - A swapping `g` acts on `w` as `σ`, since `σ⁻¹ g` fixes `A`. It sends the triple to
    `x_A(1) x_m(σ w) x_B(1)`. With the relation and the commutations this equals
    `x_B(1) x_m(σ w + r) x_A(1) = x_B(1) x_m(w) x_A(1)`.
- `pieceTriple_zero_fixed hlam g hg`: for `λ` in the fixed field of the pair stabilizer, the
  triple `x_B(0) x_m(λ) x_A(0) = x_m(λ)` is fixed by the pair stabilizer.

## Provenance

These are internal lemmas, built from published Library results and the helper modules of
this task and of Worker 185. They make no new mathematical assertion.
