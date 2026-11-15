# Unitarizability of Speh representations

Module `Langlands.Representation.Classification.SpehUnitarizabilityProof`.

The theorem `Langlands.Classification.spehUnitarizability` proves the published
proposition `Langlands.Classification.SpehUnitarizability.{uF, uV} F T` (module
`Langlands.Representation.Classification.SpehUnitarizabilityStatement`). It needs no
hypotheses and holds for every prime `p`, every `F : PadicField.{uF} p`, every
`T : F.TopologicalData`, and independent universes `uF` and `uV`.

The statement is Tadic 1986, Appendix, Theorem A.8. Let `d = (delta, k)` be a
discrete-series datum, meaning `d.IsDiscreteSeries`. Then every actual smooth
representation `π` of `GL_(k r)` with carrier universe `max uF uV` that satisfies
`d.IsSpeh π`, that is, every representative of `u(delta, k)`, is unitarizable
(`IsUnitarizable π.representation`). The statement does not assume that a Speh
quotient exists. It is a claim about every representation satisfying the published
Speh relation.

## Proof

The proof is a single composition. The published theorem
`spehUnitarizabilityLocalReduction F T` (module
`Classification.SpehUnitarizabilityReductionProof`) proves
`SpehUnitarizabilityLocalReduction F T`. That proposition is the implication

`ComplementarySeriesUnitarity → BernsteinUnitaryProductIrreducibility →
BernsteinUnitaryProductFactorUnitarity → SpehUnitarityInputs → SpehUnitarizability`,

which is Tadic's induction on the Speh length `k` (Tadic 1986, Lemma 6.2;
Badulescu 2014, Theorem 1(b)). This theorem applies it to published proofs of all
its hypotheses, every one taken at the same `p`, `F`, `T`, `uF` and `uV`:

1. `complementarySeriesUnitarity F T` (module
   `Classification.TadicComplementarySeriesProof`) proves
   `ComplementarySeriesUnitarity`. This is Tadic 1986, Proposition 2.9: unitarity
   along the complementary series and of every irreducible constituent at its end
   point.
2. `bernsteinUnitaryProductIrreducibility F T` (module
   `Classification.BernsteinUnitaryProductIrreducibilityProof`) proves
   `BernsteinUnitaryProductIrreducibility`. This is Bernstein's theorem (Tadic 1986,
   Theorem 2.5(i)): a finite normalized product of irreducible unitarizable blocks is
   irreducible and unitarizable.
3. `bernsteinUnitaryProductFactorUnitarity F T` (module
   `Classification.BernsteinUnitaryFactorProof`) proves
   `BernsteinUnitaryProductFactorUnitarity`, the weak form of Tadic 1986,
   Theorem 2.5(ii).
4. `SpehUnitarityInputs` is a conjunction of three propositions. The anonymous
   constructor `⟨_, _, _⟩` supplies each of them:
   - `spehComplementaryIrreducibility F T` (module
     `Classification.SpehComplementaryIrreducibilityProof`) proves
     `SpehComplementaryIrreducibility`: the product
     `nu^alpha u(delta,k) × nu^(-alpha) u(delta,k)` is irreducible for
     `0 < |alpha| < 1/2`.
   - `spehNeighborProductIrreducibility F T` (module
     `Classification.SpehNeighborProductIrreducibilityProof`) proves
     `SpehNeighborProductIrreducibility`: for `k ≥ 2`,
     `u(delta,k+1) × u(delta,k-1)` is irreducible (Badulescu 2014,
     Theorem 1(b)(ii)).
   - `spehNeighborProductEndpointSubquotient` (module
     `Classification.SpehNeighborProductEndpointProof`; its `F` and `T` are
     implicit) proves `SpehNeighborProductEndpointSubquotient`: when that product is
     irreducible, it is a subquotient of the end point
     `nu^(1/2) u(delta,k) × nu^(-1/2) u(delta,k)`.

All these inputs are unconditional theorems in the Library, so the composition is
unconditional too. The theorem's type is exactly `SpehUnitarizability.{uF, uV} F T`.
Its only axioms are the standard `propext`, `Classical.choice` and `Quot.sound`.

## How the reduction uses the inputs

This summarizes the published proof of `spehUnitarizabilityLocalReduction`. Its own
Markdown (`SpehUnitarizabilityReductionProof.md`) gives the details. The induction
runs on `k` for a fixed discrete series `delta`:

- For `k = 1`, a representative of `u(delta, 1)` is isomorphic to `delta`, which is
  unitarizable because `delta` is a discrete series.
- For `k = 2`, the complementary series `nu^alpha delta × nu^(-alpha) delta` is
  irreducible on `(-1/2, 1/2)`. At `alpha = 0` this follows from input 2. For
  `alpha ≠ 0` it follows from the first Speh input applied to a representative of
  `u(delta, 1)`. Input 1 then makes every irreducible subquotient at the end point
  `alpha = 1/2` unitarizable. A representative of `u(delta, 2)` is an irreducible
  quotient of that end point.
- For `k ≥ 3`, write `k = m + 1` with `m ≥ 2`. By induction `u(delta, m)` is
  unitarizable. The products `nu^alpha u(delta,m) × nu^(-alpha) u(delta,m)` are
  irreducible on `(-1/2, 1/2)`: for `alpha ≠ 0` by the first Speh input, and for
  `alpha = 0` by input 2. Input 1 makes every irreducible subquotient at
  `alpha = 1/2` unitarizable. The product `u(delta, m+1) × u(delta, m-1)` is
  irreducible (second Speh input) and occurs as a subquotient at that end point
  (third Speh input), so it is unitarizable. Both factors are irreducible and
  Hermitian (Library `SpehHermitian`), so input 3 makes the factor
  `u(delta, m+1)` unitarizable.

## Provenance

This is the target theorem of Task 5099. The composition follows Tadic's local
induction (Tadic 1986, Lemma 6.2 with Appendix A.4 and A.6, as presented in
Badulescu 2014, Theorem 1(b)). It does not follow Tadic's original global argument
for Theorem A.8. The proof route may differ from the literature. The statement itself
is unchanged.
