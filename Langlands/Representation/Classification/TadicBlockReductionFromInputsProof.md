# Proof of Tadić's Lemma 4.8(ii) from its inputs

Author: Worker 5121. Module
`Langlands.Representation.Classification.TadicBlockReductionFromInputsProof`.

## Result

```lean
theorem Langlands.Classification.tadicBlockReductionFromInputs :
    TadicBlockReductionFromInputs.{uF, uV} F T
```

for every prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p`, `T : F.TopologicalData`
and independent universes `uF`, `uV`. This is exactly the published proposition of
`Classification/TadicBlockReductionStatement`:
`TadicBlockReductionInputs F T → TadicBlockReduction F T`, where the inputs are
`BernsteinUnitaryProductIrreducibility` (Tadić 1986, Theorem 2.5(i)),
`BernsteinShiftedHighestDerivativeUnitarity` (2.5(iii)), `ComplementarySeriesUnitarity`
(Proposition 2.9), `UnlinkedSocleProductIrreducibility` (Zelevinsky 1980, Proposition 8.5),
`TadicRectangleSoclePrime` (Tadić, Proposition 3.8) and
`UnitarizableSocleHermitianSymmetry` (Tadić §2.1–2.4). The theorem adds no other hypothesis;
its axioms are `propext`, `Classical.choice` and `Quot.sound`. It applies
`TadicBlockReductionAssembly.tadicBlockReductionFromInputs`.

## The implemented proof

The route differs from Tadić's (it does not split the support into lines, does not use
Lemma 4.7 or Theorem 2.5(ii)); it uses the shifted highest derivative, the factorial ring
`R` and the Hermitian symmetry for all supports at once. The proof is a strong induction on
`m` (`BlockReductionAt m`, module `TadicBlockReductionAssembly`, theorem `step`). Fix `m`,
assume `(U^m)`, and let `π` be irreducible unitarizable on `GL_(m+1)`, not a Zelevinsky socle
of any `a(n,d)^ρ` with `ρ` unitary. Notation: `R` is the published ring
`gradedInductionRing` with its proved laws; `[X]` is the class of `X`; for a parameter
`q = (ρ, n, d, α)` (`RParam`), `rect q = a(n,d)^(ν^α ρ)`; a *unitary family* (`UFamily`) is
a multiset of parameters with `ρ` unitary, `n > 0`, `|α| < 1/2`, invariant under `α ↦ -α`,
whose socles of `a(n,d)^ρ` are unitarizable.

1. **Multisegment.** By the published Zelevinsky exhaustion, `π = ⟨a⟩` with
   `deg a = m + 1`.
2. **Derivative** (`exists_derivative_family`). By `TadicBlockDerivative`
   (Theorem 2.5(iii) and the weak form of Zelevinsky 8.1), the shifted highest derivative
   `π'` is irreducible unitarizable on `GL_M`, `M < m + 1`, and, if `M > 0`, a socle of
   `ν^(1/2) a⁻`. If `M = 0` then `a⁻ = 0`. Otherwise either `π'` is itself a socle of some
   `a(n,d)^ρ` (a member of `X_m`), or the induction hypothesis at `M - 1` factors `π'` into
   members of `X_(M-1)`. In both cases `TadicBlockBlocks.isTadicXBlock_analysis` (which uses
   2.5(i), 2.9 and Zelevinsky 8.5 for the complementary products) and
   `TadicBlockRing.cls_product` give `[π'] = ∏_{J_X} [⟨rect q⟩]` for a unitary family `J_X`,
   so by the product rule (Zelevinsky 8.4, `isZelevinskySocle_of_cls_eq_prod_rectCls`) and
   injectivity of `a ↦ ⟨a⟩`, `ν^(1/2) a⁻ = ∑_{J_X} rect q`.
3. **Decomposition.** Extending segments (`eq_extSeg_dropLast_add`),
   `a = ∑_{J_X'} rect q + φ` with `J_X' = J_X` lengthened (`d ↦ d + 1`) and `φ` the
   one-element segments of `a`.
4. **Hermitian symmetry.** `UnitarizableSocleHermitianSymmetry` gives `a.map reflSeg = a`.
   The sum over `J_X'` is reflection invariant, hence so is `φ`.
5. **Completion** (`onePoint_decomposition`). There are one-element families `L, R` of
   Steinberg-type rectangles `a(k,1)^(ν^β ρ)` with `φ + ∑_L rect = ∑_R rect`; they are
   unitary families (`TadicBlockSteinberg`).
6. **Degrees.** Every rectangle of `J_X'` has base degree at most `m`
   (`base_degree_le`): a single rectangle with `α = 0` of degree `m + 1` would make
   `π = ⟨a(n,d+1)^ρ⟩`, excluded by hypothesis (`not_rect_eq`). Hence `J_X'` is a unitary
   family by `(U^m)`.
7. **Two products.** `X_L = π × ∏(blocks of L)` and `X_R = ∏(blocks of J_X' + R)` are
   irreducible (2.5(i)); blocks are `⟨rect q⟩` for `α = 0` and complementary products
   `ν^α σ × ν^(-α) σ` for the pairs (unitarizable by 2.9). By Zelevinsky 8.4 both are socles
   of `a + ∑_L rect = ∑_{J_X'+R} rect`, hence
   `[π] ∏_L [⟨rect q⟩] = ∏_{J_X'+R} [⟨rect q⟩]`.
8. **Primes.** Each `[⟨rect q⟩]` is prime by `TadicRectangleSoclePrime`. `R` is a domain with
   units `±1` (`segmentPolynomialComparison`), so `[π]` is `±∏_J [⟨rect q⟩]` for some
   `J ≤ J_X' + R` (`exists_le_associated_of_dvd_prod_map`); the minus sign is impossible
   because the coefficient of the label of `π` would be negative. By the product rule,
   `a = ∑_J rect q`.
9. **Pairing.** `a` is reflection invariant, so by uniqueness of rectangle decompositions
   (`map_refl_eq_of_sum`) `J` is reflection invariant; by step 6's argument every base
   degree is at most `m`, so `J` is a unitary family.
10. **Factorization.** The blocks of `J` (`famBlocks`: `⟨a(n,d)^ρ⟩` with `nd deg ρ ≤ m`, and
    complementary products `ν^α ⟨a(n,d)^ρ⟩ × ν^(-α) ⟨a(n,d)^ρ⟩` with `0 < α < 1/2`) are
    members of `X_m` (`famBlocks_isTadicXBlock`), have total rank `m + 1`, and their
    normalized product `Y` over the block shape `listShape` is irreducible (2.5(i)) with
    `[Y] = ∏_J [⟨rect q⟩] = [π]`. Irreducible representations with equal classes are
    isomorphic (`nonempty_iso_of_cls_eq`), so `π ≅ Y`, which is the conclusion of
    `TadicBlockReduction` at `m`.

## Helper modules

`TadicBlockRing`, `TadicBlockDerivative`, `TadicBlockSteinberg`, `TadicBlockCombinatorics`,
`TadicBlockBlocks` and `TadicBlockReductionAssembly`, each described in its own Markdown.

## Source

M. Tadić 1986 (`tadic-1986-unitary`, SHA-256
`08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`), Lemma 4.8(ii) and its
proof, printed pp.360–361 (PDF pp.27–28); Zelevinsky 1980 (`zelevinsky-1980-induced-ii`).
The Lean proof follows the alternative route above.
