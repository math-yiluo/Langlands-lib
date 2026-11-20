# Common-field constructions for Herbrand theory

`Langlands.LocalFactor.Ramification.Herbrand.GeneralTransport` defines the
following objects in the namespace `Langlands.Ramification.Local`.

## Upper subgroup in an ambient field

Let `K₀` be a complete, locally compact ultrametric normed field with a
nontrivial norm and a `ValuativeRel`. The hypothesis `hbase` identifies norm
comparison on `K₀` with valuative comparison. Let `K` be finite over `K₀`, and
let `Ω` be a field with a compatible tower `K₀ → K → Ω`. At a real index `v`,
`upperGroupIn K₀ K Ω hbase v` is the intersection over finite Galois
intermediate fields `M` of `Ω/K` of the preimages of their canonical upper
groups. The restriction is `absoluteFiniteRestriction K Ω M`, whose
underlying homomorphism is `AlgEquiv.restrictNormalHom M`. The finite upper
group uses `LocalField.canonicalTopologicalData K₀ M hbase`, with finiteness
over `K₀` supplied by the tower. The same finite intersection appears in
`Local.absoluteUpperRamificationGroup` and reduces to it when `Ω` is a
separable closure. The ambient definition also applies to general `Ω/K`.

This implements the finite-restriction construction in Serre, *Local Fields*
(1979), Chapter IV, §3, Remark 1, printed p. 75. The extension to an arbitrary
ambient field supports comparisons within a single common field. One can use
`K₀ = K` for a nonarchimedean local field `K` by applying
`LocalGalois.localNormedField` and its compatibility results, as in
`GeneralAbsolute.lean`.

## Integer rings and finite Galois pullback

For `f : L₁ ≃ₐ[K] L₂` with towers `K₀ → K → Lᵢ`, the input realizations
`Tᵢ : LocalField.TopologicalData K₀ Lᵢ` supply valuations and their compatible
topologies. The result applies to the canonical realizations and to the
supplied realizations used by the p-adic API. Restricting scalars to `K₀`
gives continuity of both field maps for the module topologies. A field
element has valuation strictly below one exactly when its natural powers
tend to zero. If an element of the first integer ring mapped to an element
of valuation above one, the inverse of its image would have powers tending
to zero. Continuity of `f.symm` would then place the inverse of the original
element strictly below one, a contradiction. Applying the argument in both
directions gives `map_mem_integers_iff` and the restriction `integerEquiv`.
This is the same convergence argument used for automorphisms in `LocalGalois`.

For `e : Ω₁ ≃ₐ[K] Ω₂`, `comapFiniteGalois K e M` is the image of `M` under
`e.symm`, with finiteness and Galois structure transferred along
`IntermediateField.equivMap`. Its inverse is `comapFiniteGaloisEquiv K e M`,
which acts by `e` on elements. These are internal constructions for field
transport, using the integer rings and finite Galois fields already in the
Library. The definitions use no characteristic assumption. Separability is
part of the finite Galois input for pullback, and the absolute specialization
uses a separable closure. The p-adic identification with the group in an
algebraic closure uses the separable-closure instance for the characteristic-zero
base in `Absolute.lean`.

## Lean names

General names in the left column are under `Langlands.Ramification.Local`.
The existing names on the right are under `Langlands.Ramification.HerbrandBridge`
in `TransportProof.lean`. They specialize the constructions through
`K₀ = Padic p` and `PadicField.TopologicalData.toLocalData` where applicable.

| General declaration | P-adic specialization |
| --- | --- |
| `upperGroupIn` | `upperGroupIn` |
| `mem_upperGroupIn_iff` | `mem_upperGroupIn_iff` |
| `map_mem_integers_iff` | `map_mem_integers_iff` |
| `integerEquiv` | `integerEquiv` |
| `comapFiniteGalois` | `comapFiniteGalois` |
| `comapFiniteGaloisEquiv` | `comapFiniteGaloisEquiv` |
| `comapFiniteGaloisEquiv_coe` | `comapFiniteGaloisEquiv_coe` |

The registered source `serre-1979-local-fields` has content SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
