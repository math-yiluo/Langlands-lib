# Actual minimal-Levi positive-part decay assembly

This internal supporting reduction assembles the published recurrence engine
into the existing `HasRationalPositivePartDecay` property on all points of the
actual minimal Levi. The motivating source is Waldspurger (2003), Lemma VI.2.3,
printed pp.299–301. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The interface and assembled proof are derived internal content.

`HasRationalSplitDecayInput` records the remaining family-specific inputs:
uniform weak/positive annihilators at a component point which vanishes on the
inside simple roots and is strictly positive on the outside roots; compact
weighted bounds for the full constant-term family; and a polynomial height
bound on that full family in the shifted closed chamber. These are intermediate
inputs, not additional premises asserted for the final orbit-decay statement.
The reduction does not prove their actual orbit realization. The input is
independent of the final choice of norm on the real cocharacter space. Its
compact bounds concern the full standard-Levi group; the positive part is
formed there before restriction to the minimal Levi.

The implementation uses the supplied norm on the full real cocharacter space,
the actual minimal-Levi inclusion, and polynomial pullback of right translations.
The existing compactness and empty-index standard-Levi covering yield the
height comparison and compact containment of bounded-`H₀` sets. Uniform
annihilators transfer compact bounds to the actual positive part without
requiring continuity of the positive-part family. The actual Levi Xi weight
is nonnegative and invariant under the component translation.

The finite inside and outside simple forms reproduce the original shifted
closed chamber and the full closed positive-part region. The abstract
`exists_norm_le_exp_of_decomposition` then supplies exponential decay, with
its constant enlarged to a positive one. Every standard index, including the
improper case, remains in the reduction's scope.

The assembly retains connected reductivity, maximal splitness, the generic
cocharacter, `J ⊆ simpleRelativeRoots`, the specified compatible split component,
the open compact and its actual Levi Iwasawa pair, compactness of the supplied
`K₀`, its empty-index standard-Levi Cartan covering, an arbitrary positive-definite
seminorm `N`, and a supplied closed finite matrix embedding. It introduces no
new norm-kernel compactness or structural existence premise. The family
parameter type has an arbitrary independent universe; compactness or topology
on it is unnecessary when the input compact bounds are already supplied.

The module also proves continuity of the existing actual Levi Xi function by
transporting the published `continuous_rationalXi` through the canonical
Levi-scheme point equivalence.
