# Conjugation preserves identity jets

This internal module shows that the identity jets of a group scheme are
stable under conjugation. This is the step "`G` acts on `G_n` through the
inner automorphisms `int(g)`" in SGA 3, Exposé XVI, the proof of Corollary
2.4 and Proposition 3.1. It is a step toward
`JetConjugationRepresentationStatement`.

Let `G` be a group scheme over an arbitrary scheme `S`.

- `IdentityJet.IsJetPoint.comp`: if `x` is a jet point on `V` and `c : V' ⟶ V`
  is a morphism of test schemes, then `c ≫ x` is a jet point. The
  factorization through the jet is precomposed with `c.left`.
- `IdentityJet.ideal_comap_le_of_identity`: let `φ : G.X.left ⟶ G.X.left`
  satisfy `G.identitySection ≫ φ = G.identitySection`. Then pulling back the
  order-`n` jet ideal along `φ` gives an ideal contained in it. For the ideal
  of the unit section this follows from Mathlib's `map_ker`, which gives
  `(ker e).map φ = ker (e ≫ φ) = ker e`, and the Galois connection
  `le_map_iff_comap_le`. Pullback of ideal sheaves commutes with powers
  (`IdentityJet.idealSheaf_comap_pow`), and powers are monotone.
- `IdentityJet.jetMap` and `IdentityJet.jetMap_inclusion`: such a `φ`
  restricts to a morphism of the order-`n` jet to itself, compatible with the
  jet inclusion.
- `IdentityJet.IsJetPoint.comp_of_identity` and
  `IdentityJet.IsJetPoint.comp_hom`: composing a jet point with such an
  endomorphism, in particular with any group-scheme endomorphism of `G`,
  gives a jet point. Homomorphisms preserve the unit section
  (`identitySection_naturality`).
- `IdentityJet.IsJetPoint.conj`: assume `G` is separated. If `g : U ⟶ G.X`,
  `a : V ⟶ U` and `x : V ⟶ G.X` is a jet point, then
  `(a ≫ g) * x * (a ≫ g)⁻¹` is a jet point. Base change `G` to `U.left` and
  view `g` as a section `g'` of the base-changed group `H`
  (`baseChangeBasePointsEquiv`). The test scheme `V` becomes a scheme over
  `U.left` through `a`, and `x` becomes a point `x'` of `H`, up to an
  isomorphism of test schemes with identity underlying morphism. By
  `IdentityJet.isJetPoint_baseChange_iff`, `x'` is a jet point of `H`. The
  Library's inner automorphism `H.innerIso g'` is a group-scheme
  automorphism, so `x' ≫ innerIso g'` is a jet point. Its point formula
  (`comp_innerIso_hom`) and the multiplicative base-change point
  equivalence turn it back into the stated conjugate.

The module adds no geometric input beyond the Library's identity jets, inner
automorphisms and the base-change lemmas of
`Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelReduction`.
