# Rational points of an `A₂` relative root group from induced piece triples

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.A2OrbitDescent`, namespace
`Langlands.GroupScheme.GaloisCompatiblePinningData`.

## Setting

The setting is that of modules `Rational.A2OrbitPieces` and `Rational.A2OrbitInduction`:
- `D` is Galois-compatible pinning data with pinning `p`;
- `PairOrbit m₀` is the Galois orbit of a merged root `m₀`, with `root m₀ = root p₀ + root q₀`;
- `M : PairOrbit m₀ → p.SteinbergModifiedData` are merged-root data.

The Galois transport of the merged-root maps is assumed as the hypothesis
`hMx : σ((M c).xAlpha(s)) = (M (σ • c)).xAlpha(σ s)`. This is clause 3 of
`exists_mergedPieces`.

## Definitions

- `simplePoint b c` is the rational point `x_b(c)` of the simple-root map
  `D.rootMaps b` of the pinning.
- `pieceTriple p₀ q₀ M c u w v = x_{pairB c}(u) · (M c).xAlpha(w) · x_{pairA c}(v)`. This is a
  triple in the order `q, m, p` of the published `PieceFamily.tripleProd`.

## Results

- `inducedPoint_pieceTriple M hMx u w v c`: transporting the base triple to the piece `c`
  gives `pieceTriple c (τ u) (τ w) (τ v)`, with `τ = transportElement c`. Proof: coefficient
  conjugation is multiplicative. Simple-root maps are transported by
  `RootMapsGaloisCompatible.rationalPoint` (with `D.rootMaps_compatible`), merged maps by
  `hMx`. Then apply `action_transportElement_pairA/B` and `transportElement_smul`.
- `pieceTriple_mem_pieceGroup M c u w v`: the triple lies in the published `pieceGroup` of
  `(pairA c, pairB c, (M c).alpha)`. Each factor lies in a root group of the piece
  (`rationalPoint_mem`).
- `inducedPoint_pieceTriple_commute … hcc`: transports of the base triple to distinct pieces
  `c ≠ c'` commute. The two pieces are disjoint by `pair_eq_of_mem`. Disjoint pieces commute
  by the published `pieces_commute` and `commute_of_mem_pieceGroup`.
- `exists_rootGroupPoint_pieceTriple … ha0 u w v hfix`. Assume:
  - `G` is smooth and locally of finite type over `k`, and `K/k` is finite Galois;
  - the hypotheses of `a2PieceFamily` hold;
  - `a ≠ 0`;
  - `hfix`: the base triple `x_B(u) x_m(w) x_A(v)` at `basePair m₀` is fixed by its stabilizer.

  Then there is `X ∈ U_a(k)`, the rational points of the relative root group of `a` for
  `groupHom t ≫ D.inclusion`, with `rationalExtend X` equal to `F.tripleProd` of the
  transported triples. Here `F` is `a2PieceFamily`, and the `l`-th triple is
  `pieceTriple` at `pieceEquiv m₀ l`. Proof:
  1. The induced product equals this `tripleProd`, by `inducedPoint_pieceTriple`.
  2. It is Galois-fixed, by `rationalConjugate_inducedProduct` with the commutation result.
  3. It lies in the base-changed relative root group of `a`:
     - the restriction-compatible inclusion is the base change of the composite
       (`groupHom_restrictMap_comp_inclusion`);
     - each root group of a piece lies in the restricted root group of `a`, with multiplicity
       1 for `p`, `q` and 2 for `m` (published `rootGroupPoints_le_comp`, with
       `splitPinnedOppositeFactorPairs`).
  4. Galois descent of fixed points into relative root groups
     (`exists_mem_rootGroupPoints_of_fixed`, module `Rational.OrthogonalOrbitDescent`) gives
     `X`.

## Provenance

This is an internal construction from published Library results and the task's helper
modules. It makes no new mathematical assertion. It produces the rational points of `U_a(k)`
used in the `A₂`-orbit case of `Z(k) ⊆ G(k)^+` for quasi-split simply connected groups.
