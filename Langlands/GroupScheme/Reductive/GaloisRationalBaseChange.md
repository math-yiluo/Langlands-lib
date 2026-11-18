# Scalar extensions of representations over `k` and root-span vanishing

This module connects the root-span vanishing of the Tits obstruction
(`Reductive/TitsRootVanishing`) with representations of `G` defined over the
ground field `k`. The scalar extension of a representation over `k` is
Galois-rational, so its maximal simple weights have trivial obstruction
(Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un
corps quelconque*, J. reine angew. Math. 247 (1971), Proposition 3.4 with
`D = k`, in the multiplicity-one maximal-weight case proved in
`Reductive/TitsMaximalWeight`). The module also expresses the remaining input of root-span
vanishing through representations over `k` and the weights
`δ - ∑_{i ∈ O} α_i` for a star-fixed weight `δ`.

## Declarations

### Galois-rationality (`MatrixRepresentation`)

- `universalMatrix_baseChange`: for a representation `ρ` of `G` over `k`, the
  universal matrix of its scalar extension `ρ.baseChange (algebraBaseMap k K)`
  has entries `1 ⊗ c`. Here `c` is the corresponding entry of the affine
  matrix of `ρ` at the universal point of `G`. The proof combines the
  published `affineMatrix_scalarExtensionPoint` (on a common test algebra,
  the scalar extension has the original affine matrix) with
  `affineMatrix_naturality` along `O(G) → K ⊗[k] O(G)`.
- `universalMatrix_galoisTwist_baseChange`: the Galois twist by `σ` acts on
  universal matrices through `σ ⊗ id` (`universalMatrix_galoisTwist`), which
  fixes `1 ⊗ c`.
- `GaloisPinningData.isGaloisRational_baseChange`: the scalar extension of a
  representation over `k` is `IsGaloisRational`.

### Root-span vanishing from representations over `k` (`GaloisPinningData`)

- `simpleRootSum O = ∑_{i ∈ O} α_i` for a finite set `O` of simple roots.
- `HasGroundMaximalWeight ν`: some representation of `G` over `k`, on a
  nonempty `Fin (m + 1)`, has after scalar extension to `K` the weight `ν`
  with a one-dimensional weight space, and no weight strictly above `ν`.
- `hasRationalMaximalWeight_of_ground`: this implies
  `HasRationalMaximalWeight ν`, by `isGaloisRational_baseChange`.
- `starOrbitSum_eq_simpleRootSum`: a star-orbit sum is the simple-root sum of
  the orbit.
- `titsObstructionValue_eq_zero_of_mem_rootSpan_of_ground`: assume `hspan`
  and `K/k` Galois. Let `δ` be star-fixed, and suppose that for every
  finite set `O` of simple roots, `δ - simpleRootSum O` satisfies
  `HasGroundMaximalWeight`. Then the Tits obstruction vanishes on every
  star-fixed element of the integral root span. Apply
  `titsObstructionValue_eq_zero_of_mem_rootSpan`: `O = ∅` gives `δ`, and the
  star orbits give the `δ - s_q`.

The intended `δ` is the sum of the positive roots (the published
`IntegralWeylVector.positiveRootSum`), with witness `Λ^{N - |O|}` of the
adjoint representation, where `N` is the number of positive roots. Those
facts are not proved here.
