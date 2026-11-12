# Inflation of finite Galois Weil classes from the norm square

Author: Worker 5095, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`.

Let `F ⊂ E ⊂ L` be a tower of finite extensions of `ℚ_p` with `E/F` and `L/F` Galois.
The tower is given by embeddings `f : F → E` and `g : E → L` such that `L → \bar F`
extends `E → \bar F` (hypothesis `hF1`). This module proves the inflation law of
Tate, *Number theoretic background* (1979), (1.2.4), printed p.5 (PDF p.14):

`inf α_{E/F} = [L : E] · α_{L/F}`

for the actual Weil pushout classes `finiteGaloisClass` of the Library
(`Langlands.Weil.Local.FiniteGaloisPushout`).

The Library already has this statement as
`FiniteGaloisTower.relativeInflation_finiteGaloisClass` (Worker 1839,
`Langlands.Weil.Local.FiniteGaloisTower`), but there it assumes the transfer square
`ExtensionWeilTransferReciprocityStatement` (hypothesis `hT`), which is not proved.
Here `hT` is replaced by the norm square `reciprocityUnits_extensionWeilMap`
(`Langlands.Weil.Local.ExtensionNormReciprocity`), which is derived from the
single-field reciprocity relations. The cohomological input is
`GroupExtensionPushout.cohomologyClass_inflate_norm`
(`Langlands.GroupTheory.ExtensionNormInflation`). Tate cites Artin–Tate, Chapter XIII §3,
Theorem 6 for this law.

All declarations are in `Langlands.Weil.Local.FiniteGaloisTower`.

## Declarations

### `cohomologyClass_inflate_norm_of_comp`

This is `cohomologyClass_inflate_norm` with the composite quotient `π ∘ q` replaced by
any `q'` with `π.comp q = q'`. The norm hypothesis is stated for elements `x` of
`ker q` together with a proof that `x ∈ ker q'`:
`ι (r' ⟨x, hx⟩) = ∏_{h ∈ ker π} h • r x`.
The proof substitutes `q' = π ∘ q` and applies `cohomologyClass_inflate_norm`.
It mirrors the Library's `cohomologyClass_inflate_pushout_of_comp`.

### `towerKernelEquiv` (definition)

The kernel of `towerRestriction : Gal(L/F) → Gal(E/F)` is in bijection with
`Gal(L/E)`, where `L` is an `E`-algebra through `g`. An element of the kernel fixes
`g(E)` (`towerRestriction_apply`), so it is an `E`-algebra automorphism. Conversely,
an `E`-automorphism restricts scalars to an `F`-automorphism that restricts to the
identity on `E`. Both composites are the identity on underlying maps.

### `prod_towerKernel_smul`

For `b ∈ Lˣ`, the product of `h • b` over `h` in the kernel of the tower restriction
is `N_{L/E}(b)`, viewed in `Lˣ`. `L/E` is Galois (`IsGalois.tower_top_of_isGalois`).
Mathlib's `Algebra.norm_eq_prod_automorphisms` gives
`algebraMap E L (N_{L/E} b) = ∏_{τ ∈ Gal(L/E)} τ b`, and `towerKernelEquiv`
reindexes the product.

### `norm_absoluteBaseConjugation_towerCorrection`

Let `κ = towerCorrection F E L f g` be the element of `G_F` comparing the direct and
composite closure isomorphisms. Its restriction to `L`
(`absoluteBaseConjugation F L (g ∘ f) hL κ`) fixes `g(E)`
(`absoluteBaseConjugation_towerCorrection`, which uses `hF1`). So it is an
`E`-algebra automorphism of `L`, and `N_{L/E}(κ|_L a) = N_{L/E}(a)`
(`Algebra.norm_eq_of_algEquiv`).

### `towerNorm`

This is the norm hypothesis for the tower. Write `q_L`, `q_E` for the finite Galois
quotients of `W_F`, and `r_L`, `r_E` for the inverse reciprocity maps on their kernels
(`finiteGaloisKernelReciprocity`). For every `x ∈ ker q_L` that also lies in `ker q_E`:

`ι(r_E x) = ∏_{h ∈ ker(Gal(L/F) → Gal(E/F))} h • r_L x`, where `ι : Eˣ → Lˣ` is
induced by `g`.

Proof. Write `x = ι_{F,L}(w)` with `w ∈ W_L`. Since conjugation by `κ` is an
automorphism of `W_L` (`finiteGaloisAbsoluteConjugation`), `w = κ v κ⁻¹` for some
`v ∈ W_L`. Then
`x = κ ι_{F,L}(v) κ⁻¹ = ι_{F,E}(ι_{E,L} v)`, by
`extensionWeilMap_finiteGaloisAbsoluteConjugation` and `extensionWeilMap_comp`.
Hence:

- `r_E x = e_E(ι_{E,L} v)⁻¹ = N_{L/E}(e_L v)⁻¹` (norm square);
- `r_L x = e_L(κ v κ⁻¹)⁻¹ = κ|_L(e_L v)⁻¹` (`reciprocityUnits_finiteGaloisAbsoluteConjugation`).

By `prod_towerKernel_smul` the right side is `N_{L/E}(κ|_L(e_L v))⁻¹`. This equals
`N_{L/E}(e_L v)⁻¹` by `norm_absoluteBaseConjugation_towerCorrection`.

### `relativeInflation_finiteGaloisClass_of_norm` (main theorem)

Let `eE`, `eL` be reciprocity candidates satisfying `GeometricWeilReciprocityRelation`
for the canonical topological data of `E` and `L`. Then

`relativeInflation F E L 2 (finiteGaloisClass F E f hE eE heE) =
  [L : E] • finiteGaloisClass F L (g ∘ f) hL eL heL`.

The statement is that of `relativeInflation_finiteGaloisClass`, without `hT`. The proof
follows the Library proof, with `cohomologyClass_inflate_norm_of_comp` and `towerNorm`
in place of `cohomologyClass_inflate_pushout_of_comp` and `towerTransfer`.
`relativeInflation_cohomologyClass` identifies actual inflation with inflation of the
normalized cocycle. The kernel of `Gal(L/F) → Gal(E/F)` has `[L : E]` elements by the
index computation copied from the Library proof.

## Provenance

The main theorem is Tate (1979), (1.2.4), first identity, printed p.5. The other
declarations are internal lemmas for its proof. The route via the norm square and
`cohomologyClass_inflate_norm` is the identity-representative case of the cocycle
computation in Artin–Tate, Chapter XIII §3, Theorem 6, as documented in
`Langlands.GroupTheory.ExtensionNormInflation`.
