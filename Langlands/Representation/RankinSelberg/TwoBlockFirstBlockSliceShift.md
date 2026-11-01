# Determinant transport for the mixed first-block quotient

Module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockSliceShift`.
Namespace `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient`.
Author: Worker 117. The product-measure transport pattern follows Worker 27's
published `TwoBlockFirstBlockMeasures`; that module supplies the measures used
here. The group and quotient definitions are the published first-block data.

This internal construction supplies a normalization step in the proof of
`TwoBlockFirstBlockQuotientIntegrationStatement`. It defines left multiplication
by a first-block matrix on the actual mixed quotient, proves that it preserves
every compatible quotient measure for the restriction-normalized mixed Haar,
and proves the exact pushforward from the zero determinant slice to slice `k`.
It does not yet compare the fiber kernels or prove the disintegration identity.

## Objects and normalization

Fix any canonical p-adic field `F` (in arbitrary universe `uF`) and positive
two-block shape with first and second sizes `a = m 0 + 1` and `b = m 1 + 1`.
Write `G = GL_(a+b)` and `L = diag(GL_a^0,N_b)` for the published
`mixedSubgroup F h`. The actual mixed quotient is `L \ G` with its Borel
structure. The ambient measure is `generalLinearHaar F.Carrier t`. The measure
`normOneHaar F (m 0)` is exactly the pullback of ambient first-block Haar under
the open inclusion `GL_a^0 ↪ GL_a`, and `mixedHaar F h` is the pushforward of
its product with second-block unipotent Haar.

For any `z : GL_a`, let `Z = firstBlockEmbedding h F.Carrier z = diag(z,1)`.
The homeomorphism `mixedLeftShift F h z` sends `[g]_L` to `[Zg]_L`.
This map is well defined because conjugation by `Z` preserves `L`.
Its implementation first applies the published quotient automorphism induced
by conjugation by `Z`, and then right translates by `Z`. The representative
formula is `mixedLeftShift_mk`.

No subgroup Haar measure can be rescaled independently in this construction:
all preservation results use the specified `normOneHaar` and `mixedHaar`.
The base measure `νL` may be any measure compatible with this fixed pair.

## Implemented proof

1. Ambient conjugation by `z` is the composition of left multiplication by `z`
   and right multiplication by `z⁻¹`. Two-sided Haar invariance makes it
   measure preserving.
2. Determinant norm is invariant under conjugation. Restrict ambient Haar to
   the norm-one subgroup, use `MeasurePreserving.restrict_preimage_emb`, and
   compare the pushforwards through the open subgroup inclusion. The exact
   restriction identity `map_normOneHaar` and injectivity of pushforward under
   a measurable embedding prove `map_normOneHaar_conjugation`.
3. Conjugation by `diag(z,1)` acts on the product coordinates of `L` as
   `(u,n) ↦ (zuz⁻¹,n)`. Transport the product measure through
   `mixedSubgroupHomeomorph`. The first factor is invariant by the preceding
   lemma and the second factor is unchanged, proving
   `map_mixedHaar_conjugation`.
4. Both the ambient conjugation and its restriction to `L` have Haar modulus
   one, as follows from their exact measure preservation and
   `mulEquivHaarChar_eq`. The published
   `IsCompatible.map_quotientAutomorphism` therefore gives measure preservation
   on `L \ G`. Compose with the compatible measure's right invariance to obtain
   `measurePreserving_mixedLeftShift`.
5. Quotient induction and multiplicativity of determinant give
   `determinantOrder (mixedLeftShift z q) = ord(det z) + determinantOrder q`.
   If `ord(det z) = k`, the preimage of the mixed slice `k` is exactly the
   mixed slice `0`. Restricting the measure-preserving homeomorphism yields

   ```text
   map (mixedLeftShift F h z) (νL.restrict (determinantSlice F h 0))
     = νL.restrict (determinantSlice F h k).
   ```

   This is `map_restrict_mixedLeftShift`, with no scalar or density.

## Provenance and limits

The motivating original is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions* (1983), registered source
`jpss-1983-rankin-selberg`, Section 4.6, printed page 412, displays (5) and (6).
Its SHA-256 is
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page 412 was visually checked at zero-based PDF index 46 (one-based
page 47); `resource_pdf` takes one-based page arguments. The source equation
has zero outer determinant slice, inner slice `k`, and no displayed scalar.
This module's quotient homeomorphism and its explicit Haar normalization are
internal proof constructions for the published target, rather than separately
named results in JPSS. No source erratum note was found in the earlier audit.

The fiber-kernel transport, the normalized zero-slice tower and analytic
conclusions remain obligations of the full integration proof. This module
establishes only the mixed-quotient transport described above; it introduces
no representation, character or convergence assumptions.
