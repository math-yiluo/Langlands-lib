# Reconstructing a character from finite coefficient values

Author: Worker 706; verified and documented for the exact descent proof by
Worker 1366. This derived construction reconstructs an actual character,
using the universal-value and natural-value interfaces of the companion
modules.

Fix an arbitrary affine `G/k`, an ambient field extension `K/k`, a finite
Galois intermediate field `L`, and a unit `v` in `L ⊗[k] Coord G`. Suppose
its image under `tensorEmbed` equals `tensorValue G K ψ` for an actual
character `ψ` of `G_K`. This equality is the hypothesis `hv` throughout the
construction; the final descent theorem supplies it from the finite
coefficient lemma.

`modelValue G L v B` evaluates `v` at any point over a commutative
`L`-algebra `B`, with compatible `k`-algebra structure.
`modelValue_compare` uses `tensorEval_compare`, `hv` and `tensorValue_eval`
to identify its image in `K ⊗[L] B` with the original character value at
the extended point.

`modelHom` proves the identity and multiplication laws for these values.
The map `B → K ⊗[L] B` is injective by
`Algebra.TensorProduct.includeRight_injective` applied to the injective
field map `L → K`. Its induced map on units is therefore injective. After
applying that map, `modelValue_compare` reduces both laws to the existing
group homomorphism laws for point extension and `valueE ψ`. Thus these
are consequences of scalar extension, rather than extra assumptions on
`v`. `modelValue_naturality` separately follows from naturality of tensor
evaluation.

For every `A : CommAlgCat.{u} L`, `finiteApp` uses the existing `pointE`
comparison to obtain a natural group homomorphism from affine points of
the actual base change `G_L` to `Aˣ`. Affineness of `G_L` follows from the
pullback construction. `finiteApp_naturality` combines naturality of
`pointE` with that of `modelValue`.

`finiteCharacter` applies `AffineCharacterNaturalValues.character` to
this family and gives an actual element of `rationalCharacters G_L`.
`finiteCharacter_affineValues` gives its values on the actual affine
points of `G_L`. Finally, `finiteCharacter_values` rewrites through
`valueE_apply` and cancels the `pointE` equivalence to recover
`modelValue` on every `L`-algebra. No finite-type, smoothness,
connectedness, reductivity or splitting hypothesis on `G` occurs.
