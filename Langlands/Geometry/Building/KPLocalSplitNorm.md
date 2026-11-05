# Bounded split-torus norms over local intermediate fields

Let `F` be a nonarchimedean local field, let `E` be a finite intermediate
extension of its inertia fixed field inside `SeparableClosure F`, and let `L`
be a finite intermediate extension of `E` in that same closure. The valuation
on each field is the restriction of the prescribed ambient spectral valuation.
The second restriction is `nestedIntermediateValuation`; the module checks that
it extends the first and is invariant under every `E`-automorphism of `L`.

The published `separableInertiaUnitNormSurjectivity` provides a scalar unit of
valuation one over `L` whose field norm is any prescribed unit of valuation one
over `E`. The explicit scalar hypothesis of the split-torus norm reduction is
therefore discharged by an actual proof, in either characteristic and at an
arbitrary universe.

When `L/E` is Galois, `inertiaBoundedNorm` is the actual rational point norm
restricted to the character-valuation kernels of an affine commutative group
scheme over `E` and its actual base change to `L`. It is proved surjective when
the group is a split torus. This follows by the coordinate reduction implemented
in `KPSplitNorm`, with the scalar theorem just described.

This is internal infrastructure for the split norm step of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12, printed pp.89–90
(PDF pp.120–121). It asserts neither a comparison of distinct splitting fields
nor independence of the zero subgroup.
