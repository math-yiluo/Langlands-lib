# Actual relative reflections from full-kernel normalizers

This internal adapter works over every field `k : Type u`, in arbitrary
characteristic. Let `G` be affine, `T` a split torus, and `i : T → G` a monic
embedding. Supply an actual relative root `a` and a rational torus-normalizing
point `n` whose whole-character action sends `a` to `-a`. If `n` centralizes
the full scheme-theoretic character kernel of `a`, then
`IsSplitTorus.isRelativeReflection_of_mem_kernelCentralizer` proves that its
actual quotient class in `relativeWeylGroup i` satisfies `IsRelativeReflection`
in `a`.

The proof applies the published full-kernel integral-difference theorem through
`IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer`. It obtains an actual
integral cocharacter pairing to two with `a` and the reflection formula on the
entire character lattice. `RelativeRootSystem.corootFunctional` extends this
pairing to a rational linear functional on the existing actual root span.
The implemented proof checks its value at the original root vector and proves
equality with the quotient action on the spanning family of actual root
vectors. Thus it satisfies the existing reflection predicate without any
root-system realization or rank-one quotient premise.

For any smooth affine representative `j : C → G` of the full character-kernel
centralizer, its canonical identity-component torus is
`kernelCentralizerIdentityTorus i hT a j hj`. A supplied normalizer `n` in that
component maps to an ambient normalizer by the canonical map.
`isRelativeReflection_kernelCentralizerIdentityNormalizerMap` proves the same
ambient relative-reflection conclusion whenever this mapped action negates
`a`. The all-test centralizer membership needed above is furnished by
`kernelCentralizerIdentityNormalizerMap_mem`.

The entry definition `kernelCentralizerIdentityNormalizerReflection` retains
that exact mapped quotient class together with its proved relative-reflection
property. It does not choose a new point or replace the supplied normalizer.
The ambient group need not be reductive for these implications, and maximality
of the split torus or closedness of `j` is not an additional hypothesis. The
smooth affine assumptions on `C` are those of the imported canonical
identity-component construction. Neither theorem constructs a normalizer or
proves its root-negation property, nor establishes integral opposite factors.

The provenance is internal composition of the named published lattice,
root-span and kernel-centralizer constructions. This is a focused comparison
needed when a lifted normalizer in the opposite-factor argument must be
identified with the actual ambient root reflection.
