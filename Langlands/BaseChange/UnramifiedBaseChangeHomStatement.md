# Existence and uniqueness of the unramified base-change homomorphism

Module `Langlands.BaseChange.UnramifiedBaseChangeHomStatement`.
`Langlands.BaseChange.UnramifiedBaseChangeHomStatement.{u, v}` is a proposition-valued
definition (statement 7 of Task 7424). It states an unproved obligation; it is neither
proved nor assumed in this module.

## Statement

The module repeats, as local instances declared for every `PadicField` over every prime,
the canonical topology, valuative relation and local-field structure of the field, and the
canonical topology, topological-group, Hausdorff, Borel measurable and Borel space
structures on `GL_n`, as in `Langlands/Representation/Unramified/HeckeOperators.lean`, so
that the spherical Hecke algebras of `F` and of `E` are the Library's own.

For every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{u} p`, every
`E : PadicField.{v} p` and all `l r : ℕ`, there is exactly one (`∃!`) complex algebra
homomorphism `b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r` with
`IsUnramifiedBaseChangeHom F E l r b` (module `Langlands.BaseChange.UnramifiedHecke`):
for every Satake parameter `s : Eigenvalues (r + 1)`, the Satake character of `F` at `s`
composed with `b` is the Satake character of `E` at `Eigenvalues.power s l` (the entries
of `s` raised to the power `l`); in terms of the Satake transforms,
`S_F(b φ)(s) = S_E(φ)(s^l)`.

The statement assumes no relation between `E` and `F` other than the common prime `p`:
it is not restricted to unramified extensions of degree `l`, and it includes `l = 0`
(where `b φ` is `S_E(φ)(1, …, 1)` times the unit).

## Source

Henniart-Lemaire (2011), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
printed page + 8): §I.1.3, printed p. 6 ("Via les isomorphismes de Satake pour `H_E` et
pour `H_F`, est défini un homomorphisme d'algèbres `b : H_E → H_F`"), and §I.3.1, printed
p. 25 (`b` defined by `S_F(b(φ))(X_1, …, X_n) = S_E(φ)(X_1^l, …, X_n^l)`, using the Satake
isomorphism of their reference [57], Laumon 1996, 4.1).

Derivation (provenance: derived from this source). Existence: the substitution
`X_j ↦ X_j^l` maps symmetric Laurent polynomials to symmetric Laurent polynomials, so
`b = S_F^{-1} ∘ (X_j ↦ X_j^l) ∘ S_E` is an algebra homomorphism, which needs the
surjectivity of `S_F` onto `ℂ[X_1^{±1}, …, X_n^{±1}]^{S_n}`; evaluating at `s` gives the
defining identity of `IsUnramifiedBaseChangeHom`. Uniqueness: if `b` and `b'` both satisfy
it, then for every `s`, the Satake character `ωF` of `F` at `s` and the Satake character
`ωE` of `E` at `s^l` (both exist by statement 6, `SatakeCharacterStatement`, part (a))
satisfy `ωF (b φ) = ωE φ = ωF (b' φ)`, so `b φ - b' φ = 0` by statement 6, part (b).

This existence and uniqueness is what makes the fundamental-lemma statement 9
(`Langlands.BaseChange.FundamentalLemmaStatement`), which quantifies over all `b` with
`IsUnramifiedBaseChangeHom F E l r b`, non-vacuous.
