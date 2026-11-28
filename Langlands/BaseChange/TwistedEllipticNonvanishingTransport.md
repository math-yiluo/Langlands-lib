# Nonvanishing of twisted traces on the σ-elliptic set, transported along ring isomorphisms

`TwistedSupercuspidalEllipticNonvanishingStatement` is stated for a cyclic algebra `E'` over a
nonarchimedean local field `F` of characteristic zero that is a field. It says that the twisted
trace `φ ↦ tr (τ'(φ) ∘ A)` of an irreducible supercuspidal representation `τ'` of `GL_n(E')`
is nonzero on some Schwartz–Bruhat function supported in the σ-elliptic set. This module carries
that conclusion along an isomorphism `b : E ≃+* E'` to `GL_n(E)`, where `E` is only a
commutative `F`-algebra. The intended case is `E = F_v ⊗_F E₀` for a cyclic extension of number
fields `E₀/F₀` at a place `v` with a single place `w` above it, and `E' = E₀,w`
(`Langlands.BaseChange.UniquePlaceTensorCompletion`).

## Setting

`F` is a field and `E`, `E'` are `F`-algebras with topologies, `E'` a field, `σ`, `σ'`
automorphisms of `E` and `E'` over `F`. `b : E ≃+* E'` is a ring isomorphism, continuous with
continuous inverse, with `b (algebraMap F E a) = algebraMap F E' a` (hypothesis `hι`) and
`b (σ x) = σ' (b x)` (hypothesis `hσ`). `generalLinearRingEquiv b hb hb'`
(`Langlands.BaseChange.ConcordanceRingEquiv`) is the entrywise isomorphism
`GL_n(E) ≃ₜ* GL_n(E')`.

## Results

- In `isSigmaElliptic_generalLinearRingEquiv_iff`, `δ ∈ GL_n(E)` is σ-elliptic iff its image under
  `generalLinearRingEquiv b` is σ'-elliptic. Both sides ask for a regular elliptic
  `γ ∈ GL_n(F)` associated with `δ`. Association is transported by
  `generalLinearRingEquiv_isNormAssociated_iff` with the identity of `F`, and the identity
  fixes `γ`.
- `SigmaIntertwiner.ofGeneralLinearRingEquiv` sends a σ-intertwiner `A` of the pullback
  `τ' ∘ GL_n(b)` to a σ'-intertwiner of `τ'` with the same underlying linear equivalence.
  Every element of `GL_n(E')` is `GL_n(b) g`, and `GL_n(b)` carries `entrywiseAut σ` to
  `entrywiseAut σ'` by `hσ`. `ofGeneralLinearRingEquiv_toLinearMap` records that the linear map
  is unchanged.
- `exists_sigmaEllipticSupported_twistedDistribution_ne_zero_of_ringEquiv` assumes
  `TwistedSupercuspidalEllipticNonvanishingStatement` (hypothesis `hNV`). Let `F` be a
  nonarchimedean local field of characteristic zero and `E'` a field with its module topology
  that is a cyclic `F`-algebra for `σ'` of degree `l` (`IsCyclicAlgebra σ' l`), and `0 < n`. Let
  `ψ : GL_n(E) →* GL_n(E')` be the homomorphism underlying `generalLinearRingEquiv b` (the
  hypothesis `hψ` states this equality; `ψ` is a variable so that a caller may supply the
  homomorphism in another syntactic form). Let `τ'` be an irreducible supercuspidal
  representation of `GL_n(E')`. Then for every σ-intertwiner `A` of `τ' ∘ ψ` and every Haar
  measure `μ` on `GL_n(E)` there is a Schwartz–Bruhat function `φ` on `GL_n(E)` supported in
  the σ-elliptic set with `tr ((τ' ∘ ψ)(φ) ∘ A) ≠ 0` for `μ`.

  The proof applies `hNV` to `τ'`, the σ'-intertwiner `SigmaIntertwiner.ofGeneralLinearRingEquiv A`
  and the Haar measure `μ.map κ`, `κ = generalLinearRingEquiv b`
  (`ContinuousMulEquiv.isHaarMeasure_map`). This gives `φ'` on `GL_n(E')` supported in the
  σ'-elliptic set with nonzero twisted trace. Take `φ = φ' ∘ κ`. Its support condition is the
  previous bullet. The change of variables `twistedDistribution_comp_equiv`
  (`Langlands.BaseChange.TwistedLocalGroupTransport`) identifies its twisted trace for `μ`
  with that of `φ'` for `μ.map κ`. The instances on `GL_n(E')` (Borel σ-algebra, Hausdorff,
  locally compact, totally disconnected) are those used in the statement.

## Sources

The statement transported here is a test-function form of Arthur–Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1, Lemma 2.12(i) and
Proposition 2.2 (source `arthur-clozel-1989-base-change`), as explained in the Markdown of
`TwistedSupercuspidalEllipticNonvanishingStatement`. The transport along ring isomorphisms is a
change of variables derived here. It is needed because the Library realizes the local
component at a place with a single place above it on `GL_n(F_v ⊗_F E₀)`, while the statement
is about a field.
