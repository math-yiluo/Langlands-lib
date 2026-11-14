# The `A₂`-orbit case of `Z(k) ⊆ G(k)^+`

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.A2OrbitUnits`, namespace
`Langlands.GroupScheme.GaloisCompatiblePinningData`.

The setting and notation are those of module `Rational.A2OrbitGeneration`: pinning data
`D`, `t : S ⟶ D.torus`, the merged root `m₀` of `p₀ ≠ q₀`, the base piece `c₀` with roots
`A`, `B`, and merged-root data `M`. The module also uses the accepted field lemmas of Worker
185 (`Langlands.FieldTheory.QuadraticFixedField`, module
`FieldTheory.QuadraticFixedFieldCoordinates`).

## Hypotheses

The two main results assume all of the following:
- `G` is smooth and locally of finite type, `K/k` is finite Galois, and `(D.torus)_K` is
  split;
- `i = groupHom t ≫ D.inclusion` is a maximal split torus and a closed subgroup (`hf`, `hic`);
- `D.inclusion` is a closed subgroup representing the centralizer of `i` (`hjc`, `hcent`);
- the pinned coroots span the cocharacter lattice (`hspan`; it holds for simply connected
  groups);
- `i` has opposite factor pairs (`hE`), and `a` and `-a` are relative roots;
- the piece hypotheses `hm₀`, `hS`, `hp₀`, `hq₀`, `hpq`, `hline`, and `hM`, `hMx` on `M`;
- `D.action σ₀ p₀ = q₀` for some `σ₀`.

## Results

- `transportElement_basePair`: the transport element of the base piece is `1`.
- `pair_mem_orbit hσ₀ c`: both roots of every piece lie in the Galois orbit of `A`. Use
  `transportElement` and `swapElement`.
- `mem_orbitGoodUnits_of_fixed hσ₀ u w hw hfix`. If the base triple `x_B(u) x_m(w) x_A(u)`
  is fixed by the pair stabilizer and `w ≠ 0`, then `w` is a good unit at `A`
  (`orbitGoodUnits`).
- `simpleCorootProduct_mem_of_a2 hσ₀ hnc hc`, **the `A₂`-orbit case**. Assume also `hnc`:
  `x_A(1)` and `x_B(1)` do not commute. Then for every orbit family `c` at `A`,
  `p.inclusion(∏_b b^∨(c b))` lies in `relativeRootGeneratedExtension k K i`, the image of
  `G(k)^+` in `G(K)`.

## Proof of `mem_orbitGoodUnits_of_fixed`

1. By `exists_rootGroupPoint_pieceTriple`, the stabilizer-fixed triple gives `X ∈ U_a(k)`.
   Its scalar extension is the product of the transported triples, with merged coordinates
   `τ_l w` (units, since `w ≠ 0`). The triple `x_m(1)` gives `X₀ ∈ U_a(k)`, with coordinates
   `1` (`pieceTriple_zero_fixed`, `simplePoint_zero`).
2. `X` and `X₀` are nontrivial, by `SplitPinning.tripleProd_ne_one`.
3. `hE` gives opposite pairs `(A₁, B₁)` and `(A₀, B₀)`. Let
   `t₀ = A₁ X B₁ (A₀ X₀ B₀)⁻¹`. It lies in `G(k)^+`
   (`relativeRoot_subgroup_le_generated` for `a` and `-a`).
4. `exists_rationalTorusPart` gives a pinned-torus point `x` with
   `rationalExtend t₀ = p.inclusion(x)`. For characters `ω` with `⟨ω, q_l^∨⟩ = 0` for all `l`,
   `ω(x) = ∏ₗ (τ_l w)^⟨ω, p_l^∨⟩`.
5. Take the witness `c b = fundamentalWeightEval b x`. The pairings with simple coroots are
   given by `fundamentalWeightBasis_pairing`.
   - `c` is equivariant (`fundamentalWeightEval_action`).
   - For `b` off the orbit of `A`, no piece root equals `b` (`pair_mem_orbit`), so `c b = 1`.
   - Its coroot product is `x` (`simpleCorootProduct_fundamentalWeightEval`), whose image is
     `rationalExtend t₀`.
   - `c A = w`. The root `B` of a piece never equals `A`, and `A` occurs as a `p`-root only in
     the base piece (`pair_eq_of_mem`). So the product reduces to the base factor, where
     `τ = 1` (`Finset.prod_eq_single`).

## Proof of `simpleCorootProduct_mem_of_a2`

Let `H` be the root stabilizer of `A`, `H'` the pair stabilizer, and `σ` the swap element.
Then `H ≤ H'`, `[H' : H] = 2`, and `σ ∈ H' \ H`. Let `E` and `L₀` be the fixed fields of `H`
and `H'`.

1. The commutator scalar `r` lies in `E` and satisfies `σ r = -r`
   (`commutatorScalar_fixed`, `commutatorScalar_swap`). Moreover `r ≠ 0`, since otherwise
   `x_A(1)` and `x_B(1)` would commute.
2. By `QuadraticFixedField.exists_sub_conjugate_eq` there is `w₁ ∈ E` with `w₁ - σ w₁ = r`.
   Then `w₁ ∉ L₀`.
3. Every unit `λ ∈ L₀` is a good unit: use `pieceTriple_zero_fixed` and the previous
   lemma with `u = 0`.
4. Every `w₁ + b` with `b ∈ L₀` is a good unit. Its difference with its `σ`-conjugate is `r`,
   and it lies in `E`. Use `pieceTriple_one_fixed` and the previous lemma with `u = 1`.
5. `c A` lies in `E`, by equivariance. By `QuadraticFixedField.unit_decomposition`,
   `c A = a'` or `c A = a' (w₁ + b)` with `a' ∈ L₀^×` and `b ∈ L₀`. Here `w₁ + b ≠ 0` since
   `w₁ ∉ L₀`. So `c A` is a good unit, since good units form a subgroup.
6. Conclude with `mem_of_mem_orbitGoodUnits`.

## Provenance

The theorem is the `A₂`-orbit (`SU(3)`-type) case of Steinberg's theorem `Z(k) ⊆ G(k)^+` for
quasi-split simply connected groups. See Platonov–Rapinchuk, *Algebraic Groups and Number
Theory* (1994), §7.2, printed p. 406, registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`. There `G_k^+ = G_k` is attributed to
Steinberg for quasi-split simply connected groups. The proof given here is internal:
- rank-one Weyl elements are computed over a splitting field;
- their torus parts are read off through fundamental weights;
- generation follows from the quadratic decomposition of `E^×`.

Hypothesis `hnc` (noncommutation of the two simple root groups at `1`) is supplied by a
separate lemma.
