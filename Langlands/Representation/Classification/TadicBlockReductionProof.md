# Proof of Tadić's Lemma 4.8(ii) (factorization into members of `X_m`)

Author: Worker 5121. Module
`Langlands.Representation.Classification.TadicBlockReductionProof`.

## Result

```lean
theorem Langlands.Classification.tadicBlockReduction :
    TadicBlockReduction.{uF, uV} F T
```

for every prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p`, `T : F.TopologicalData`
and independent universes `uF`, `uV`. This is exactly the published proposition
`TadicBlockReduction` of `Classification/TadicExhaustionLemmasStatement` (Tadić 1986,
Lemma 4.8(ii), existence part): for every `m`, under `(U^m)` (`TadicSocleUnitarity m`),
every irreducible unitarizable representation `π` of `GL_(m+1)` that is not a Zelevinsky
socle of any `a(n,d)^ρ` (`tadicMultisegment ρ n d hd`) with `n > 0` and `ρ` unitary is
isomorphic to a normalized product, over some block shape of `m + 1`, of members of `X_m`
(`IsTadicXBlock m`). The theorem has no hypothesis; its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## The implemented proof

The theorem applies `TadicBlockReductionAssembly.tadicBlockReduction_of_inputs` to the
following six proved Library results:

| Input | Proposition | Source | Lean proof |
|---|---|---|---|
| `hA` | `BernsteinUnitaryProductIrreducibility` | Tadić 1986, Theorem 2.5(i) (Bernstein) | `bernsteinUnitaryProductIrreducibility` |
| `hB3` | `BernsteinShiftedHighestDerivativeUnitarity` | Theorem 2.5(iii) | `bernsteinShiftedHighestDerivativeUnitarity` |
| `hC` | `ComplementarySeriesOpenIntervalUnitarity` | Proposition 2.9, open-interval clause | `complementarySeriesOpenIntervalUnitarity` |
| `hD` | `UnlinkedSocleProductIrreducibility` | Zelevinsky 1980, Proposition 8.5 | `unlinkedSocleProductIrreducibility` |
| `hE` | `TadicRectangleSoclePrime` | Tadić 1986, Proposition 3.8 | `TadicRectanglePrime.tadicRectangleSoclePrime` |
| `hF` | `UnitarizableSocleHermitianSymmetry` | Tadić 1986, §2.1–2.4 | `unitarizableSocleHermitianSymmetry` |

All six are in the namespace `Langlands.Classification`; their proofs are imported from the
modules `BernsteinUnitaryProductIrreducibilityProof`,
`BernsteinShiftedHighestDerivativeUnitarityProof`, `TadicComplementarySeriesUnitarityProof`,
`UnlinkedSocleProductIrreducibilityProof`, `TadicRectangleSoclePrimeProof` and
`UnitarizableSocleHermitianSymmetryProof`.

Of Tadić's Proposition 2.9 only the clause for the open interval is used: if the
complementary products `ν^α σ × ν^(-α) σ` of an irreducible unitarizable `σ` are irreducible
for `|α| < α₀`, they are unitarizable there. It is applied with `α₀ = 1/2` to socles `σ` of
`a(n,d)^ρ`, `ρ` unitary (`TadicBlockBlocks.tadicComplementaryProduct_isUnitarizable`). The
endpoint clause of 2.9 (unitarizable constituents at `α₀`) is not needed; for this reason the
helper modules `TadicBlockBlocks` and `TadicBlockReductionAssembly` take the hypothesis
`ComplementarySeriesOpenIntervalUnitarity` rather than the full `ComplementarySeriesUnitarity`.

`tadicBlockReduction_of_inputs` is a strong induction on `m` whose step
(`TadicBlockReductionAssembly.step`) is the argument described in steps 1–10 of
`TadicBlockReductionFromInputsProof.md`; in summary, for `π = ⟨a⟩` (Zelevinsky exhaustion):

1. The shifted highest derivative of `π` (Theorem 2.5(iii)) is irreducible unitarizable of
   smaller rank; by the induction hypothesis and `TadicBlockBlocks.isTadicXBlock_analysis`,
   `ν^(1/2) a⁻` is the sum of the rectangles `a(n,d)^(ν^α ρ)` of a unitary family.
2. Lengthening those segments writes `a` as that sum (with `d ↦ d + 1`) plus one-element
   segments; by the Hermitian symmetry `a` is invariant under the reflection, and the
   one-element part is completed by Steinberg-type rectangles (`TadicBlockSteinberg`).
3. Two irreducible products (Theorem 2.5(i); the blocks with `α ≠ 0` are complementary
   products, unitarizable by the open-interval clause of 2.9 and irreducible by Zelevinsky
   8.5) are socles of the same multisegment (Zelevinsky 8.4), which gives an equation
   `[π] ∏_L [⟨rect q⟩] = ∏_{J'} [⟨rect q⟩]` in the Grothendieck ring `R`.
4. The classes `[⟨rect q⟩]` are prime (Proposition 3.8), `R` is a domain with units `±1`,
   so `[π] = ∏_J [⟨rect q⟩]` for a sub-family `J`, which is again a reflection-invariant
   unitary family whose base degrees are at most `m` (the case of one rectangle `a(n,d)^ρ`
   of degree `m + 1` is the excluded case).
5. The blocks of `J` (`TadicBlockBlocks.famBlocks`: `⟨a(n,d)^ρ⟩`, and complementary products
   `ν^α ⟨a(n,d)^ρ⟩ × ν^(-α) ⟨a(n,d)^ρ⟩` with `0 < α < 1/2`) are members of `X_m`; their
   normalized product is irreducible with class `[π]`, hence isomorphic to `π`.

The route differs from Tadić's printed proof: it does not split the support into lines and
does not use Lemma 4.7 or Theorem 2.5(ii); it uses the shifted highest derivative, the ring
`R` and the Hermitian symmetry for all supports at once.

## Helper modules

`TadicBlockRing`, `TadicBlockDerivative`, `TadicBlockSteinberg`, `TadicBlockCombinatorics`,
`TadicBlockBlocks` and `TadicBlockReductionAssembly`, each described in its own Markdown.
`TadicBlockBlocks` and `TadicBlockReductionAssembly` are edited by this contribution: the
complementary-series hypothesis is weakened to `ComplementarySeriesOpenIntervalUnitarity`,
`step` takes the six inputs separately, and `tadicBlockReduction_of_inputs` and
`complementarySeriesOpenIntervalUnitarity_of` are added. The published
`TadicBlockReductionAssembly.tadicBlockReductionFromInputs` keeps its type and is now
derived from `tadicBlockReduction_of_inputs`.

## Source

M. Tadić, *Classification of unitary representations in irreducible representations of
general linear group (non-archimedean case)*, Ann. Sci. ÉNS (4) 19 (1986), 335–382
(`tadic-1986-unitary`, SHA-256
`08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`): Lemma 4.8(ii) and its
proof, printed pp.360–361 (PDF pp.27–28); Theorem 2.5; Proposition 2.9 (p.350);
Proposition 3.8. A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
Ann. Sci. ÉNS (4) 13 (1980), 165–210 (`zelevinsky-1980-induced-ii`): Propositions 8.4–8.5
(p.196).
The Lean proof follows the alternative route above.
