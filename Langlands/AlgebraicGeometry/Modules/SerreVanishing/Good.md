# Uniform vanishing and exact sequences

This internal module develops the formal properties of the predicate used in
the two-bundle Serre vanishing proof. It does not assert that an arbitrary
coherent module satisfies this predicate.

`pairTwist N₁ N₂ a b` sends a module `M` to the actual tensor product
`(M ⊗ tensorPow N₁ a) ⊗ tensorPow N₂ b`.
`Good f N₁ N₂ M` says that one natural number bounds both exponents so that
every positive-degree `DerivedSections.relativeCohomology f` of these modules
is zero.

The module proves invariance under isomorphism, goodness of a zero module,
closure under short exact extensions, and passage from all factors of a
coherent filtration to its last term. Tensoring with either power preserves
short exactness because tensoring with a locally free module of rank one is
an equivalence. The extension argument uses exactness at the middle term of
the right-derived long exact sequence, taking the maximum of two thresholds.

The final lemma treats an arbitrary morphism after a functor that preserves
short exact sequences. It factors the morphism through its image. The first
short exact sequence gives zero cohomology of the image when the source in
degree `i` and kernel in degree `i+1` vanish; the second gives zero cohomology
of the target when the cokernel in degree `i` also vanishes.

These are derived categorical steps for this proof, rather than a separate
claim from the literature. They implement the dévissage argument described
in the paired documentation of `ProperAmplePairSerreVanishingStatement`,
using the Library's right-derived exact sequence and actual tensor functors.
