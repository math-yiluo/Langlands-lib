# Character values of a root and its orbit partner

Worker 244. This internal unit supplies the character-value comparison left
open in `RootPartnerFields`. Work over fields `k,L : Type u` with an algebra
`k → L`, a commutative group scheme `T`, an affine group scheme `G`, and a
homomorphism `j : T.toGrp → G`. Absolute roots refer to the actual base change
of this homomorphism to `L`.

`characterValue_partner` says that if a coefficient automorphism `σ` over `k`
moves `β` to `β'`, the value of `β'` at a base-changed original-field affine
point is `σ` applied to the value of `β`. It is the published Galois
character-value formula. `characterValue_sum` says that when `μ = β + β'`,
its value is the product of the two root values. Neither lemma assumes a
finite extension or rational-point density.

Now assume `L/k` is finite Galois. The centralizer torus is affine for the
descended-character assertion. Assume `G` is locally of finite type,
`T_L` is split, `j_L` is a closed immersion, and a finite-indexed root datum
of this same homomorphism is supplied. Require every actual absolute root
to have nonzero Galois orbit sum. Let `β'` be an actual orbit partner of `β`
in the sense of `RootPartnerFields.IsRootPartner`, and let
`μ = β + β'` be an actual root. Write `E = rootOrbitField k L j β` and
`E₀ = rootOrbitField k L j μ`.

Retain supplied inclusion-compatible algebra and scalar-tower instances
between `E₀`, `E` and `L`, together with the separable quadratic instances
on `E/E₀`. The published `RootPartnerFields` results construct these field
inclusions and quadratic and separability facts under the displayed
root hypotheses. `characterValue_norm` proves that the image in `E` of
the `μ` value equals the `β` value times its conjugate over `E₀`.
Choose `σ` moving `β` to `β'`. Published `conjugation_apply` identifies
its action on `E` with quadratic conjugation. The two elementary
character-value lemmas then prove the identity inside the ambient field
`L`; the inclusion `E → L` is injective.

`HasCharacterNormValues` is the corresponding Prop-valued condition on the
actual descended characters `rootOrbitCharacter` of `T_E₀` and `T_E`.
It quantifies over every original rational point of `T`, with those
points extended to the respective value fields. `hasCharacterNormValues`
proves this condition by the published
`rationalCharacterEval_rootOrbitCharacter` comparison.

The provenance is internal composition of the named published
Galois-descent, root-partner field and character-addition results.
There is no characteristic or field-cardinality restriction, and no
use of rational-point density. This is a character-value identity.
It does not construct quotient or doubled-root coordinates, prove a
separation condition on character values, or construct coherent SU3
coordinates, their homomorphism or their coroot map.
