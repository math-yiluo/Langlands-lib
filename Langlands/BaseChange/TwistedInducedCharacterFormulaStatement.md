# The twisted induced character formula at σ-regular points

This module states, without proof, the twisted case of Henniart–Lemaire (2011),
II.4.5, formula (3), printed p. 88 (PDF p. 96).

## The statement

`TwistedInducedCharacterFormulaStatement.{u, v, uW}` quantifies over
nonarchimedean local fields `F` (universe `u`) and `E` (universe `v`), any
characteristic, with `E` an `F`-algebra carrying the `F`-module topology, and
`σ : E ≃ₐ[F] E` with `IsCyclicAlgebra σ l`. It further quantifies over a
positive rank `n`, a block shape `B`, and block representations `P i` of
`GL_{n_i}(E)` on spaces `W i` in universe `uW`. Each `P i` is admissible and
irreducible, with a σ-intertwiner `A i : P i ≅ P i ∘ σ`.

Let `δ ∈ GL_n(E)` be norm associated (`IsNormAssociated`) with a regular
semisimple `γ ∈ GL_n(F)`. Let `m : Fin k → B.Levi F` be a Levi class system for
`γ` (`IsLeviClassSystem`). Let `d : Fin k → B.Levi E` satisfy, for every `j`:

- `x⁻¹ δ σ(x) = leviEmbedding (d j)` for some `x ∈ GL_n(E)`, so `d j` is a
  σ-conjugate of `δ` lying in `M(E)`;
- `N(d j i) = m j i` in `GL_{n_i}(E)` for every block `i`, with the Library's
  `cyclicNorm` and `baseChange`.

Suppose the Levi tensor representation `B.blockTensor P` has twisted character
value `b j` at `d j` for `A₁ ⊗ ⋯ ⊗ A_r` (`leviTensorIntertwiner σ B A`), in the
sense of the Library's `HasTwistedCharacterValue`. Then the normalized product
induction `(LocalFieldData.ofInstances E).normalizedProductInduced B P` has
twisted character value

`∑ j, |D_{G/M}(m j)|_F^{-1/2} * b j`

at `δ` for the induced intertwiner `ι(A) = inducedSigmaIntertwiner σ B A`. The
weight is `relativeDiscriminantWeight` from `InducedCharacterFormulaStatement`.
It is the ordinary relative discriminant at the norm, as in the source's (3).

## Relation to the source

Henniart–Lemaire take `δ ∈ T(E)` σ-regular for a maximal torus `T` of `M` over
`F`. They sum `|D_{G/M}(N(δ)_η)|_F^{-1/2} Θ^B_Ξ(δ_η)` over `η ∈ W`, where
`δ_η = g_η⁻¹ δ g_η` with `g_η ∈ G(F)`. Then `N(δ) ∈ T(F)` and
`N(δ_η) = g_η⁻¹ N(δ) g_η`. The classes of the `N(δ_η)` run once through the
`M(F)`-classes in `M(F)` conjugate to `N(δ)` (see `LeviClassSystem.md`). Two
elements of `M(E)` with equal blockwise norms are σ-conjugate in `M(E)`. In each
block this is the Library's `twistedConj_of_cyclicNorm_conj_of_field`
(Arthur–Clozel 1989, Chapter 1, Lemma 1.1). The
twisted Levi character is invariant under σ-conjugation in `M(E)`. Hence each
term of the source equals the term with the given `d j`, and the twisted
character of the induced representation is invariant under σ-conjugation of
`δ`. This is how the statement here, for every `δ` norm associated with a
regular semisimple `γ`, corresponds to the source. An empty Levi class system
gives the value zero. This is the source's vanishing outside the `δ` whose norm
orbit meets `M(F)`.

As in the ordinary statement, irreducibility of the factors replaces the
source's finite type hypothesis, and the Levi values are hypotheses. The
Library does not prove this statement, and consumers use it only as an explicit
premise.
