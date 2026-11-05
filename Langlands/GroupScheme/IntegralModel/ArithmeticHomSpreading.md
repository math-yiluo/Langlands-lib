# Spreading supplied homomorphisms over enlarged finite S-integer rings

This internal construction uses finite coefficient descent of actual group-scheme
homomorphisms and the exhaustion of a number field by its actual finite S-integer
rings. All objects use the arbitrary common universe `u`.

The existing `numberFieldSIntegersMap`, bundled by `CommRingCat.ofHom`, sends
each integer-ring element to the same element of the number field. `integerInclusion_generic` proves that this map preserves the
canonical generic inclusion. `exists_integer_contains_fg_over` chooses finitely
many generators of an algebra over a prescribed S-integer ring, contains those
generators in one finite stage, and takes its union with the prescribed set of
places. The resulting ring contains both the initial ring and every generator.
The adjoin universal property then contains the whole algebra. This argument
does not require the initial S-integer ring to be finitely generated over the
ring of integers.

The private comparison associativity lemma identifies the two isomorphisms from
a triple pullback to its direct pullback. It proves equality of the underlying
scheme maps by their two pullback projections; it retains every actual base map.

`enlargeModel F M hST` pulls the prescribed integral model back along this
coefficientwise integer-ring inclusion, with the canonical direct generic-fibre
comparison. `smooth_enlargeModel` preserves optional smoothness by pullback
stability.

`exists_enlarged_hom F S M N f` starts with two prescribed actual integral
models over the same finite S-integer ring and the supplied generic homomorphism
`f`. The target structural morphism must be locally of finite presentation.
The source is already flat, quasi-compact and quasi-separated, and the target
is separated, because they are integral models with affine structural maps.
The result gives a finite `U` containing `S` and an actual
`IntegralModel.Hom` extending this same `f` between the two canonical
`enlargeModel` pullbacks. Its `generic_comm` is the equality for the supplied
maps and isomorphisms, not only an existential isomorphism of arrows.

The proof first conjugates `f` by the two prescribed generic-fibre
isomorphisms and applies `Descent.FiniteCoefficient.homModel`. It embeds the
resulting finitely generated coefficient algebra into an enlarged actual
S-integer ring. Pulling its homomorphism back and conjugating by the
direct/iterated comparison isomorphisms gives the desired integral
homomorphism. Naturality and the triple-comparison associativity lemma carry
the finite coefficient recovery equality to the canonical arithmetic generic
square. Composing with the prescribed generic-fibre isomorphisms recovers the
original `f`. `enlargedHomData` chooses these actual data from the proven
existence.

This construction requires prescribed integral models. It does not assert
closed immersion of the extending homomorphism or any reductive, parabolic or
connected fibre property. These remain obligations of the full simultaneous
spreading theorem.
