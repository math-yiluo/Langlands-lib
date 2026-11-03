# Tori and normalizing points in full root-kernel centralizers

This is an internal construction from the published all-test centralizer,
represented-subgroup factorization, maximal-split-torus lifting and
normalizing-point interfaces. It supplies the actual torus embedding and the
transport of normalizers needed when working inside a represented root-kernel
centralizer. It does not construct that representative or a root-flipping point.

Over an arbitrary base scheme, `IsNormalizingPoint.comp` uses the published
naturality of inner automorphisms to postcompose a normalizing point along a
group-scheme homomorphism, retaining its torus automorphism.
`normalizerPointsMap` bundles this operation as a group homomorphism for an
actual factorization `iH ≫ j = iG`. It is injective when the underlying map of
objects over the base for `j` is monomorphic. If the underlying torus embeddings
are monomorphic, `weylAction_normalizerPointsMap` identifies the actions on
every actual character, using the existing inverse-precomposition convention.
No field, reductivity or character-lattice presentation is required here.

`RelativeRoot.torusCentralizer_le_kernelCentralizer` restricts all-test
commutation from the whole torus to its actual character kernel.
`range_le_kernelCentralizer` then uses commutativity of the torus to establish
containment of its actual image. The kernel remains the full scheme-theoretic
kernel, including nonreduced tests. No nonzero-character, primitive-character,
splitness or smoothness premise enters either containment.

If `j : C ⟶ G` represents this kernel centralizer,
`RelativeRoot.kernelCentralizerTorus` factors the original torus map into `C`
using the published `IsRepresentedBy.factorHom`. Its composite with `j` is the
original map. Over an arbitrary field, if `j` is a closed subgroup and the
original torus is maximal split in `G`,
`IsMaximalSplitTorus.kernelCentralizerTorus` applies the published general
maximality-transport theorem to this specific containment.

`RelativeRoot.kernelCentralizerNormalizerMap` maps the normalizers in `C` to
normalizers of the original torus in `G`. Its underlying point is exactly
postcomposition with `j`, so representability puts it in the same all-test
kernel centralizer. The corresponding Weyl-action theorem preserves the action
on the entire character lattice. These conclusions are independent of any
connectedness or reductivity claim for `C`.

The proof route is wholly internal: it composes the published inner-conjugation
naturality lemma in `Rational.BruhatCoveringReduction`, the commutative-image and
factorization lemmas in `Rational.LeviFactorization`, the general closed-subgroup
maximality theorem in `Rational.MaximalSplitTorusSubgroup`, and the actual kernel
and all-test definitions in `Rational.RootSubgroup`. Intrinsic reflection
existence still requires a suitable geometric representative with a nontrivial
action inside the appropriate connected centralizer. This file proves no such
existence, root negation, or identity-component structure.
