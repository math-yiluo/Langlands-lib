# Local Weil groups along an embedding of p-adic fields

Author: Worker 53. This is a definition and construction contribution.

## Content

Fix a prime `p`, two `PadicField` objects `F` and `E` in independent
universes, and an algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`,
the abstract form of a finite extension `E / F`. Write `ι` for the published
injective map `extensionGaloisMap F E f : G_E → G_F`, `r` for the published
relative residue degree `extensionResidueDegree F E f = [k_E : k_F]`
(usually written `f`, a letter that names the embedding here), and
`n` for the published degree `extensionDegree F E f = [E : F]`. This module
constructs the map of actual local Weil groups `W_E → W_F` and proves its
degree, inertia, norm, image and topological properties.

Residue comparison.

- `extensionIntegers_isIntegral` proves that the integer ring of `E` is
  integral over that of `F` along `f`. `extensionClosureEquiv_mem_closureIntegers`
  proves that the published closure isomorphism `extensionClosureEquiv` (the
  bijective lift of `f` to algebraic closures) maps the actual closure integer
  ring of `F` exactly onto that of `E`. Both directions use integrality over
  the integer rings, via Worker 9's `closureIntegers_integral`.
- `extensionClosureIntegerEquiv` is the resulting ring isomorphism of closure
  integer rings. `extensionClosureResidueEquiv` is the induced isomorphism of
  their residue fields. `extensionResidueClosureEquiv` transports it, through
  Worker 9's `localResidueClosureEquiv` for `F` and for `E`, to an isomorphism
  `AlgebraicClosure k_F ≃+* AlgebraicClosure k_E`.
  `extensionResidueClosureEquiv_algebraMap` proves that it lies over the
  published residue map `extensionResidueMap F E f : k_F → k_E`.
- `extensionResidueGaloisMap : G_{k_E} →ₜ* G_{k_F}` is Mathlib's
  `Field.absoluteGaloisGroup.mapOfAlgebra` for this comparison.
  `extensionResidueClosureEquiv_galoisMap` is its defining compatibility, and
  `extensionResidueGaloisMap_injective` proves injectivity.
- `localResidueMap_extensionGaloisMap` proves the key square
  `res_F ∘ ι = extensionResidueGaloisMap ∘ res_E`: the actual residue actions
  of `G_E` and `G_F` (from the published `Assembly`) commute with the Galois
  maps along `f`. The proof evaluates both sides on residues of closure
  integers with Worker 9's `absoluteResidueHom_residue` and the published
  `extensionClosureLift_galoisMap`.
- `extensionResidueGaloisMap_arithmetic` and `extensionResidueGaloisMap_geometric`
  prove that the arithmetic and geometric Frobenius of `k_E` map to the `r`-th
  powers of those of `k_F`. This uses `q_E = q_F ^ r`
  (`extensionResidueCardinality`).
  `toProfiniteIntegers_extensionResidueGaloisMap` deduces, by continuity and
  density of `ℤ` in `Ẑ`, that under the finite-field comparisons the map is
  multiplication by `r` on `Ẑ`. `localResidueDegree_extensionGaloisMap`
  combines this with the square: `deg_F (ι σ) = r · deg_E σ` in `Ẑ`.

The Weil map.

- `extensionWeilMap : localWeilGroup E →ₜ* localWeilGroup F` sends a pullback
  element `(σ, m)` to `(ι σ, r m)`. It lands in the pullback for `F` by
  `localResidueDegree_extensionGaloisMap`. It is continuous on the inherited
  subgroup topologies.
- `localProjection_extensionWeilMap` states that projection to `G_F` after the
  map is `ι` after projection to `G_E`. `localDegree_extensionWeilMap` and
  `localDegreeInt_extensionWeilMap` state that the geometric degree is
  multiplied by `r`.
- `extensionWeilMap_injective` follows from injectivity of `ι` and of the
  pullback projection.
- `extensionWeilMap_mem_localInertia` proves that an element of `W_E` maps
  into `I_F` exactly when it lies in `I_E`, since `r > 0`.
  `localInertia_eq_comap_extensionWeilMap` restates this as
  `I_E = j⁻¹(I_F)`, with `j` the Weil map.
- `localNormCharacter_extensionWeilMap` proves `ν_F ∘ j = ν_E` for the
  published norm characters: `q_F ^ (-(r m)) = (q_F ^ r) ^ (-m) = q_E ^ (-m)`.
  `localUnramifiedCharacter_extensionWeilMap` proves that the unramified
  character of `F` with value `z` pulls back to that of `E` with value `z ^ r`.

Image, index and topology.

- `extensionResidueFieldAlgHom` embeds `k_E` into the closure of `k_F` over
  the residue map. `extensionResidueGaloisMap_fixes` proves that every element
  in the image of `G_{k_E}` fixes this image of `k_E`.
  `extensionResidueDegree_dvd_of_mem_range` deduces that if a power
  `Frob_F ^ m` of geometric Frobenius lies in that image, then `r ∣ m`.
  Its private helper uses the published finite-field facts that the
  restriction of geometric Frobenius to a finite extension of degree `d` has
  order `d`.
- `extensionWeilMap_range` proves that the image of `W_E` is exactly the
  inverse image in `W_F` of the image of `G_E`. Given `w ∈ W_F` with
  projection `ι σ`, the square shows that `res_E σ` maps to `Frob_F ^ m` with
  `m` the degree of `w`. Divisibility gives `m = r m'`, injectivity of the
  residue Galois map gives `res_E σ = Frob_E ^ m'`, and `(σ, m')` is a
  preimage.
- `extensionWeilMap_range_isOpen` follows, because the image of `G_E` is open
  (published `extensionGaloisMap_range_isOpen`) and the projection is
  continuous.
- `extensionWeilMap_range_index` proves that the image has index `n = [E : F]`.
  The theorem `localProjection_denseRange` from `AssemblyProof` proves that
  the actual projection `W_F → G_F` has dense image: its range is the
  inverse image of `ℤ` under the open map
  `G_F → Ẑ`, which is open by Worker 9's `absoluteResidueHom_isOpenMap`.
  A private lemma proves that pulling back an open subgroup along a
  homomorphism with dense image preserves the index. The published
  `extensionGaloisMap_range_index` then gives `n`.
  `extensionWeilMap_range_finiteIndex` is the corresponding `FiniteIndex`
  instance proof.
- `extensionWeilMap_isEmbedding` proves that the map is a topological
  embedding: on the ambient product it is the product of the closed embedding
  `ι` and the injective map `m ↦ r m` of discrete groups.
  `extensionWeilMap_isOpenEmbedding` adds openness of the image.

Together these supply the hypotheses of the published generic induction
along a map, `WeilDeligneRepresentation.parameterInduceAlong`: an open
embedding, finite-index image, `j h ∈ I_F → h ∈ I_E`, and `ν_F ∘ j = ν_E`.

## Choices and scope

The map is built from the published `extensionGaloisMap`, which depends on
Mathlib's choice-based `IsAlgClosed.lift`. No canonicity is claimed; in
particular, the identity embedding is not asserted to give the identity map
and composite embeddings are not asserted to compose. The residue comparison
is transported from that same closure isomorphism, so the stated square holds
for the actual chosen maps. Nothing here assumes reciprocity, a Weil-group
equivalence, or an independent surjectivity certificate.
This module does not compare the chosen geometric Frobenius lifts of `E` and
`F`, and it does not define restriction or induction of representations or
parameters along the map; those are separate obligations.

## Sources

This is a derived formalization of the finite-extension structure of local
Weil groups in John Tate, *Number theoretic background*, Corvallis Part II
(1979), registered source `tate-1979-number-theoretic-background`,
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

- (1.1), printed page 3 (PDF page 12): for a finite extension `E` inside the
  fixed separable closure, `W_E = φ⁻¹(G_E)`; continuity of `φ` means that
  `W_E` is open, and density of the image of `φ` gives the bijection
  `W_F / W_E ≅ G_F / G_E ≅ Hom_F(E, F̄)`. Here `E` is an abstract field with
  an embedding, so `W_E` is realized as the image of `extensionWeilMap`,
  and `extensionWeilMap_range` proves that this image is the inverse image of
  the image of `G_E`. The index statement is the cardinality form of the
  bijection: `Hom_F(E, F̄)` has `[E : F]` elements in characteristic zero.
- (1.4.1), printed page 6 (PDF page 15): `W_F` is the dense subgroup of `G_F`
  of elements acting on `k` by `x ↦ x^(q_F^m)` for some integer `m`, with
  inertia open. Applied to `E` and `F` with `q_E = q_F ^ r`, an element acting
  as `x ↦ x^(q_E^m)` acts as `x ↦ x^(q_F^(r m))`. This is the degree-scaling
  statement.
- (1.4.5), printed page 7 (PDF page 16): the subgroups `W_E` are exactly the
  open subgroups of finite index. This module proves the direction that each
  `W_E` is open of finite index, with index `[E : F]`. It does not prove the
  converse.
- (1.4.6), printed page 7 (PDF page 16): the restriction of the norm function
  from `W_F` to `W_E` is the norm function of `W_E`. Here this is
  `localNormCharacter_extensionWeilMap` for the published complex norm
  characters `q^(-degree)`.

These passages were read in the retained PDF. The geometric sign convention
and the actual field data are documented in `Assembly.md`.

## Dependencies

The construction depends on `Langlands.Weil.Local.Assembly`,
`Langlands.Weil.Local.ExtensionResidue`, `Langlands.Weil.Local.ExtensionGalois`
and `Langlands.LocalField.Normalization.Proof` (for finiteness of the integer
ring over that of `Q_p`), published at Library commit
`0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf`. The direct
`Langlands.Weil.Local.AssemblyProof` import supplies `Assembly` transitively
and the shared `localProjection_denseRange` theorem. These dependencies
transitively supply Worker 9's
`Langlands.Galois.Local.AbsoluteProof` (`closureIntegers_integral`,
`localResidueClosureEquiv`, `absoluteResidueHom_residue`,
`absoluteResidueHom_isOpenMap`), the finite-field comparison and Frobenius
facts of `Langlands.Galois.FiniteField.Frobenius` and
`Langlands.Galois.FiniteField.ComparisonProof` (`finiteRestriction`,
`geometric_restrict`, `geometric_order`, `profiniteEquivalence_symm_frobenius`),
and the generic pullback with `projection_injective` and `projection_range`
from `Langlands.Weil.AlgebraicProof`. These upstream results are used by Lean
name; their proofs are not copied. Pinned Mathlib supplies `Field.absoluteGaloisGroup.mapOfAlgebra`,
`AlgEquiv.restrictNormal_commutes`, `ResidueField.mapEquiv` and
`ProfiniteGrp.ProfiniteCompletion.denseRange`. The environment is Lean 4.34.0
with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. All new
declarations and proofs in this module are by Worker 53.
