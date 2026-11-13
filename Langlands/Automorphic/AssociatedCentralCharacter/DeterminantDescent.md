# The Hecke character of the determinant of a relative Weil representation

Author: Worker 5151.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter` (module
`Langlands.Automorphic.AssociatedCentralCharacterProof`) supplies the Galois-side input of
clauses 2 and 4 of `AssociatedCentralCharacterStatement`: at an arithmetic class family `c`,
the determinant of a continuous finite-dimensional complex representation `S` of
`W_{E/F}` is `δ ∘ τ_F` for exactly one Hecke character `δ` of `F`. This is the descent of
`det S` through the transfer `τ_F : W_{E/F} → C_F` used in Henniart (2000), §2.2.

Recall that `reciprocityCharacter c F E χ t = (χ (transfer c F E t))⁻¹` (Library module
`Langlands.ClassField.Global.RelativeWeilUnramifiedTwist` and its imports).

## `reciprocityCharacter_injective`

At an arithmetic class family, `χ ↦ reciprocityCharacter c F E χ` is injective. The
arithmetic family is destructured as `⟨I, hI, hd⟩`, and the first component of the
published `relativeWeilTransferReciprocity I hI c hd F E` says that the transfer
`W_{E/F} → C_F` is surjective. If `χ ∘ τ_F = η ∘ τ_F`, then for every idele class `a = τ(g)`
the values `(χ a)⁻¹` and `(η a)⁻¹` agree (`reciprocityCharacter_apply`), so `χ a = η a`.

## `continuous_determinantCharacter_relativeGalois`

For continuous `S`, `det S` is continuous when `W_{E/F}` carries the topology built on the
discrete `relativeGaloisTopology F E` on `Gal(E/F)`. The published
`FiniteRepresentation.continuous_determinantCharacter` gives continuity for the topology
built on the Krull topology; `krullTopology_eq_relativeGaloisTopology` identifies the two
Galois topologies, and the proof rewrites along this equality after generalizing the
topology (`key`).

## `exists_determinantCharacter_eq_reciprocityCharacter`

The inverse `(det S)⁻¹`, a continuous homomorphism `W_{E/F} → ℂˣ` by the previous lemma, is
fed to the published `transferCharacterFactorization c hc F E`, which factors it as
`δ ∘ τ_F` for a Hecke character `δ`. Unfolding `reciprocityCharacter_apply` and inverting
gives `det S = reciprocityCharacter c F E δ`.

## `existsUnique_determinantCharacter_eq_reciprocityCharacter`

Existence is the previous lemma and uniqueness is `reciprocityCharacter_injective`.
