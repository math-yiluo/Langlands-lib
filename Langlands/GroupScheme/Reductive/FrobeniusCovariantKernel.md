# Invariant vectors in actual covariant Frobenius restriction kernels

This is an internal derived construction for the Steinberg proof task.
It uses the published affine Hopf/Lie comparison, actual Frobenius quotient
coalgebra, regular translations, dynamic polynomial coordinates and augmentation
nilpotence. It asserts no new result from external literature.

For a coalgebra homomorphism `q : B →ₗc[k] C`, `regularAction q` is the unital
algebra representation of the convolution dual of `C` on `B` obtained by
pulling a functional back along `q` and applying the original `rightAct`.
The convolution multiplication agrees with composition in this convention.
The proof checks that identity and multiplication are preserved, using the
coalgebra counit and comultiplication equations.

The generic theorem `exists_annihilated_mem` takes a nilpotent ideal in a
unital algebra representation and any nonzero stable vector subspace. It
produces a nonzero vector in that same subspace annihilated by the ideal.
The proof descends through the ideal powers: if the ideal does not already
annihilate the chosen vector, apply one ideal element and descend one power.
No finite dimensionality assumption on the representation or subspace is used.

For actual affine group schemes `j : H ⟶ G` over an arbitrary field,
`restrictionAlgebra j p r` is the actual coordinate pullback to `H`, followed
by the Hopf/Lie coordinate equivalence and the height-`r` Frobenius quotient.
`restrictionCoalgebra` proves that this map respects the actual coordinate
coalgebras. In particular, its target is the quotient by the ideal generated
by the `p^r` powers of the identity augmentation ideal, with `ExpChar k p`.
`restrictionAction` applies `regularAction` to this actual map.

For any other actual affine subgroup morphism `l : P ⟶ G` and any coordinate
`χ` on `P`, `covariantKernel` is the intersection of the entire
`leftCovariantSubspace l χ` with the kernel of `restrictionCoalgebra j p r`.
No character condition on `χ` is needed. The original right translation
preserves the full covariant space. Its naturality for a coalgebra homomorphism
also preserves the kernel. These give `restrictionAction_mem_covariantKernel`
without an added stability hypothesis.

The final specialization uses the actual dynamic parabolic `P(ν)` and
`U = Standard.unipotentScheme i (-ν) ∅`. The comparison with
`Dynamic.oppositeUnipotentFrobeniusRestriction` is definitional and retains its
entire covariant subtype. Suppose `G` is smooth affine and the supplied torus
is split. If this quotient restriction is not injective at height `r`,
`exists_annihilated_of_not_injective` produces a nonzero covariant coordinate
in its kernel, annihilated under `restrictionAction` by every element of the
actual height-`r` distribution augmentation ideal of `U`. The proof obtains
positive polynomial coordinates from `Standard.unipotentPolynomialCoordinates`,
discharges nilpotence using `isNilpotent_augmentationIdeal`, and applies the
generic detection theorem to the actual kernel intersection.

All constructions allow arbitrary field universe, exponential characteristic,
height zero and zero-dimensional dynamic unipotent groups. They introduce no
restriction to rational or reduced test schemes. The final result needs neither
connected reductivity nor finite dimensionality of the entire covariant space.
It does not exclude the resulting vector, identify invariant coordinates with
Frobenius-power coordinates, prove fixed-height injectivity or a Steinberg
whole-space dimension bound, or prove `SteinbergBigCellStatement`.
