# Closed equality loci under restriction of scalars

Author: Worker 117.

This internal module provides the closed-immersion input for the represented
equality-locus proof of `WeilRestrictionDiagonalStatement`. All schemes and
commutative rings have the unrestricted universe parameter `u`. The ring
extension `A → B` is finite and projective. The module does not assume or prove
representability of the restriction of an arbitrary algebraic space.

The definition `WeilRestrictionDiagonalGeometry.affineWeilRestriction_isTerminal`
constructs a terminal-object witness for the actual affine Weil restriction of
any terminal affine scheme of locally finite type over `Spec B`. For every
scheme test over `Spec A`, the existing full-test representing equivalence
transports the unique map to the original terminal scheme to a unique map to
its Weil restriction. Injectivity of that equivalence proves uniqueness. This
is a construction of categorical terminal structure, not a new proposition
statement awaiting a proof.

Three proved geometric consequences accompany that construction:

- `property_of_mono_representsEqualizer` transfers any specified relative
  diagonal property of a presheaf to any monomorphic representative of the
  equality locus of two sections. Its argument constructs the represented
  limit fork using `RepresentsEqualizer.isLimitFork`, identifies that fork with
  the pullback of the diagonal along the pair of sections, and applies the
  given relative property to this pullback. Every scheme test is retained.
- `affineWeilRestriction_hom_isClosedImmersion` applies the Library's
  `affineWeilRestrictionMap_isClosedImmersion` to the closed map from the given
  affine scheme to the terminal upper-base scheme. The terminal witness
  identifies the Weil restriction of that terminal scheme with the terminal
  lower-base scheme. Its structure map is therefore an isomorphism, and
  composing with it gives the claimed closed structure map.
- `quasiAffineWeilRestriction_hom_isClosedImmersion` treats the existing glued
  quasi-affine Weil scheme. A closed upper-base structure map makes its source
  affine. The full presheaf representation isomorphisms for the affine and
  quasi-affine Weil schemes identify those schemes over `Spec A` by full
  faithfulness of scheme Yoneda. The closed affine structure map then transfers
  across that scheme isomorphism.

The supporting modules `WeilRestrictionDiagonalGeometry` and
`WeilRestrictionEqualizerGeometry` establish locally finite type diagonals and
quasi-affine monomorphic equality loci; their paired Markdown describes the
implemented proofs. Their theorem-only content accompanies this defined
terminal structure as supporting repository paths.

Provenance: these are internal deductions from the Library definitions of
represented equality loci, actual affine and quasi-affine Weil restrictions,
and Mathlib terminal objects, scheme Yoneda full faithfulness and closed
immersions. No external source assertion or additional hypothesis on the
algebraic space is introduced. These lemmas do not by themselves close the
full Weil-restriction diagonal target.
