# Proof of the translation part of AS 5 for quasi-split adjoint groups

`valuationBuildingQuasiSplitAdjointTranslation` proves
`ValuationBuildingQuasiSplitAdjointTranslationStatement.{u}` for an arbitrary universe `u`.

## Implemented proof

The proof is one application. The published reduction
`valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity`, in module
`Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslationReduction`, derives the
target from `QuasiSplitAdjointSimpleRootTransitivityStatement.{u}`. That proposition is
supplied by the published theorem `quasiSplitAdjointSimpleRootTransitivity`, in module
`Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityProof`.

The reduction works as follows. Let `v` be a translation of the apartment that preserves the
affine root system. Take a relative simple root `a ∈ Δ`. Then `r` and `r + a(v)` are both
values of affine roots with gradient `a`. Simple-root transitivity and axiom V 6 give
`z_a ∈ Z(F)` with `a(ν(z_a)) = a(v)` and `b(ν(z_a)) = 0` for the other `b ∈ Δ`. The product
`z` of the `z_a` satisfies `b(ν(z)) = b(v)` for every `b ∈ Δ`, hence for every relative root,
so `v` is the class of `ν(z)`.

For a simple root `a` and `u, u' ∈ U_a(k) ∖ U_{2a}(k)`, the transitivity theorem constructs
a rational point of the centralizer torus `Z`. That point commutes with `U_b(k)` for the
other simple roots `b` and conjugates `u` into `u' U_{2a}(k)`. It is obtained by Galois
descent of a family of character values. These values can be prescribed because the group is
adjoint, so the roots span the character lattice of the split torus. The Markdown of
`QuasiSplitAdjointSimpleRootTransitivityProof` describes that proof.

## Provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach`: Proposition 6.6.2 and its proof, printed
pp.231–232 (PDF pp.262–263), and Lemma 6.4.10, printed pp.227–228 (PDF pp.258–259). The
Lean proof goes through the derived proposition `QuasiSplitAdjointSimpleRootTransitivityStatement`,
not through the literal route of the book.
