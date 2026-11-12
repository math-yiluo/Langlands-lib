# Conjugating the image of a local Weil map

Author: Worker 5134. Module `Langlands.Weil.Local.ExtensionWeilRangeConjugation`.
It is a helper for the proof of `HenniartGlobalizationStatement` (Henniart 2000, §3.4).

Setting: `F` and `E` are p-adic fields (`PadicField p`) and `f : F → E` is an embedding
of `ℚ_p`-algebras. The Library's local Weil map `extensionWeilMap F E f : W_E → W_F` is
formed along the chosen embedding `extensionFieldEmbedding F E f : E → \bar F` over `F`.
Its image is `extensionWeilRange F E f`. By the Library's `extensionWeilMap_range` and
`extensionGaloisMap_range`, this image consists of the `y ∈ W_F` whose Galois projection
`localProjection F y` fixes the subfield `extensionIntermediateField F E f`, which is the
image of `E` in `\bar F`.

## Results

- `exists_galois_comp_extensionFieldEmbedding F E f ψ hψ`: let `ψ : E → \bar F` be a ring
  homomorphism with `ψ (f x) = x` for `x ∈ F`. Then there is `σ ∈ Gal(\bar F / F)` with
  `σ (extensionFieldEmbedding F E f x) = ψ x` for all `x ∈ E`. The proof makes `\bar F`
  an `E`-algebra through the chosen embedding and regards `ψ` as an `F`-algebra map. It
  extends `ψ` to an `F`-endomorphism of the normal extension `\bar F`
  (`AlgHom.liftNormal`), which is bijective because `\bar F / F` is algebraic.
- `exists_conj_mem_iff_extensionWeilRange F E f ψ hψ H hH`: let `ψ` be as above, and let
  `H` be a subgroup of `W_F` such that `y ∈ H` exactly when `localProjection F y` fixes
  `ψ x` for every `x ∈ E`. Then there is `g ∈ W_F` such that for all `y ∈ W_F`,
  `y ∈ extensionWeilRange F E f ↔ g * y * g⁻¹ ∈ H`.

  Proof. Take `σ` from the previous result, and let `J` be the image of `E` under the
  chosen embedding. The Galois elements `τ` with `σ⁻¹ τ ∈ Fix(J)` form an open set
  containing `σ`, since fixing subgroups of finite extensions are open in the Krull
  topology. The Weil group is dense in the Galois group (Library
  `localProjection_denseRange`), so this set contains `localProjection F g` for some
  `g ∈ W_F`. Then `localProjection F g` agrees with `σ` on `J`, so it sends the chosen
  embedding to `ψ`. For `y ∈ W_F`, the projection of `g y g⁻¹` fixes `ψ x` exactly when
  the projection of `y` fixes the chosen image of `x`. This gives the equivalence.

## Use

In the planned proof of `HenniartGlobalizationStatement`, `E` is a completion `E'_u` of a global
field and `f` is the completion map from `F_v`. Then `extensionWeilMap F E f` is the
Library's `completionWeilMap`, and `H` is the Weil group of a generator field `L'`. Here
`L'` is identified with `E'_u` over `F_v` by an embedding `ψ` that differs from the
chosen one. The output `g` is the input `hg` of
`ExactGrothendieckGroup.continuousInduce_characterClass_eq_along_conj`
(`Langlands.VirtualRepresentation.ExactInductionConjugation`).

## Provenance

This is the standard fact that conjugate embeddings of a local field give conjugate Weil
subgroups. It is used implicitly in Henniart (2000), §3.4. Density of the Weil group lets
the conjugating element be chosen in `W_F` rather than in `Gal(\bar F / F)`.
