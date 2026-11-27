# Compatible points under affinoid ground field extension

Let `K → L` be an isometric embedding of ultrametric normed fields, with `L`
complete. Let `φ` be a bounded map `A → B` of presented `K`-affinoid algebras.
`spectrumComparison` is the continuous map from `M(B_L)` to the subspace of
pairs in `M(B) × M(A_L)` having equal images in `M(A)`. Its two components are
restriction to `B` and pullback along the scalar extension of `φ`.

`exists_spectrumPoint` lifts a compatible pair. The two points `y ∈ M(B)` and
`x ∈ M(A_L)` give isometric maps from the completed residue field of their
common image in `M(A)` into `H(y)` and `H(x)`. The ultrametric tensor seminorm
over the common field, multiplicative domination and field realization give
isometric embeddings of `H(y)` and `H(x)` into one complete field. This field
inherits its `L`-algebra structure through `H(x)`. The evaluation of `B` in it
extends to `B_L` by the bounded universal property. On `A_L` the extension
agrees with the evaluation at `x`, since both maps agree on `A` and are
`L`-linear. Pulling the field norm back to `B_L` gives the desired point.
`spectrumComparison_surjective` expresses this for the comparison map.

The construction uses Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), §1.4, pp. 29–30 (PDF pp. 26–27), for the affinoid scalar
extension, its projection and the induced isometric residue field maps. The
compatible-pair result follows from their bounded universal properties and
the tensor amalgamation construction. The base and extension field universes
are independent. The registered source `berkovich-1993-etale-cohomology` has
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
