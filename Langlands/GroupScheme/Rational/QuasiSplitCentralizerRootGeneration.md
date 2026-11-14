# Centralizer points of quasi-split simply connected groups lie in `G(k)^+`

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.QuasiSplitCentralizerRootGeneration`.

## Results

- `exists_ne_zero_one_add_ne_zero_of_ne_one`: if `σ ∈ Aut_k(K)` is not the identity, some
  `c₀ ∈ K` has `c₀ ≠ 0` and `1 + c₀ ≠ 0`. Indeed, an element moved by `σ` is neither `0` nor
  `-1`.
- `IsQuasiSplit.nonempty_torusCentralizerTorusData`. In a quasi-split group, the centralizer of
  every maximal split torus `i` is represented by a closed torus.
  - The Library's `quasiSplitTorusCentralizerExistence` gives this for one maximal split
    torus.
  - `maximalSplitTorusConjugacy` gives `g ∈ G(k)` conjugating that torus to `i`, and
    `IsRepresentedBy.torusCentralizer_of_iso_square` transports the centralizer.
- `centralizerPoints_le_relativeRootGeneratedSubgroup_of_simplyConnected`. For `G` simply
  connected and quasi-split and `i : S ⟶ G` a maximal split torus, `centralizerPoints i`
  (the rational points `Z(k)` of the centralizer) is contained in
  `relativeRootGeneratedSubgroup i` (`G(k)^+`).
- `quasiSplitSimplyConnectedRootGeneration : QuasiSplitSimplyConnectedRootGenerationStatement`.
  For every field `k`, quasi-split simply connected `G` and maximal split torus `i`,
  `relativeRootGeneratedSubgroup i = ⊤`. This is the published statement of module
  `Rational.QuasiSplitSimplyConnectedRootGenerationStatement`, proved without additional
  premises.

## Proof of the centralizer inclusion

1. Let `C` be the closed torus representing the centralizer of `i`. Let `t : S ⟶ C` be the
   canonical factor of `i` (`torusCentralizerFactor`), so `t ≫ C.inclusion = i`.
2. Choose a finite Galois extension `K/k` splitting `C` (`torusFiniteGaloisSplitting`).
3. Use `rootDatumExistence` to choose a reduced root datum of `(C.inclusion)_K`. Then
   `GaloisCompatiblePinningData.ofRegularCocharacter` gives Galois-compatible pinning data
   `D` with `D.torus = C` and `D.inclusion = C.inclusion`. Its simple-root action is
   pairing-compatible (`ofRegularCocharacter_isPairingCompatible`).
4. The pinned coroots span the cocharacter lattice:
   - `G_K` is simply connected (`isSimplyConnectedFieldExtension`);
   - the pinning torus is split and maximal;
   - so `splitSimplyConnectedCorootSpan` applies.
5. Noncommutation `hnc` for distinct Galois-conjugate adjacent simple roots comes from Worker
   185's `SplitPinning.adjacent_unitPoint_not_commute`. Module
   `Rational.AdjacentSimpleRootNoncommutation` provides it. The scalar `c₀ ∉ {0, -1}` exists
   because the conjugating Galois element is not the identity.
6. Let `z ∈ Z(k)`. Since `C` represents the centralizer, `z = C.inclusion(z')` for a point
   `z'` of the torus (`centralizerPoints_le_torusCentralizer`).
7. Worker 185's `exists_equivariant_simpleCorootProduct` gives a Galois-equivariant unit family
   `c` with `z_K = p.inclusion(∏_b b^∨(c b))`. Here `z_K` is the scalar extension of `z`.
8. By `simpleCorootProduct_mem_of_equivariant` (module `Rational.SimpleOrbitCorootGeneration`),
   `z_K` is the scalar extension of some `y ∈ G(k)^+`.
9. Scalar extension of rational points is injective (`rationalExtend_injective'`). So
   `z = y ∈ G(k)^+`.

## Proof of the root-generation statement

`G` is connected reductive (`IsQuasiSplit.isConnectedReductive`). The published covering
corollary `relativeRootGeneratedSubgroup_eq_top_of_centralizerPoints_le` (module
`Rational.RootGeneratedCentralizerCovering`) reduces `G(k)^+ = G(k)` to `Z(k) ⊆ G(k)^+`.

## Provenance

The theorem is Steinberg's `G(k)^+ = G(k)` for quasi-split simply connected groups. It is
recalled in Platonov–Rapinchuk, *Algebraic Groups and Number Theory* (1994), §7.2, printed
p. 406, registered as `platonov-rapinchuk-1994-algebraic-groups-number-theory`. The source
recalls the statement for absolutely almost simple groups.

The proof given here is internal and covers all semisimple simply connected quasi-split
groups, all characteristics and finite fields. It reduces to the Galois orbits of simple roots:
- orthogonal orbits: products of `SL₂`-type relations;
- `A₂` orbits: an `SU(3)`-type computation in the module `Rational.A2OrbitUnits`.
