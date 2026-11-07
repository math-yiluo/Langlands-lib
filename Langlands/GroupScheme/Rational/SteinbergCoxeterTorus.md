# Faithful flatness of the actual Coxeter torus commutator

Worker 1317. This is internal support for the split Steinberg quotient proof,
derived from the actual normalizer action, the abstract Coxeter fixed-space
result, semisimple finite root index, and the published character criterion for
faithful flatness of split-torus maps. It has no external source claim.

For any monomorphic torus inclusion over any scheme, the character kernel of
`torusCommutatorEnd i n` is the fixed lattice of `weylAction i n`. The character
pullback of the difference of the normalizing automorphism and identity is zero
exactly when precomposition with that automorphism fixes the character. Composing
with its inverse identifies this with the Library's contravariant Weyl-action
convention. This proves `comap_torusCommutatorEnd_eq_zero_iff` on full actual
characters.

For a supplied split pinning, each `SimpleReflectionRepresentative.normalizerPoint`
is its actual normalizer point. Uniqueness of the induced torus automorphism
identifies its full character action with the specified simple reflection. The
ordered product `coxeterNormalizer e n` therefore acts by
`Langlands.LinearAlgebra.orderedCoxeter p.base e` for every ordering and supplied
representative family.

If the actual group is semisimple, `IsSemisimple.finite_quotient_rootSpan` and
`RootPairing.finite_quotient_rootSpan_iff_corootSpan` give finite coroot index for
the supplied root datum. The imported
`Langlands.LinearAlgebra.orderedCoxeter_eq_self_iff_eq_zero` then shows that the
ordered normalizer product fixes only the zero character. This uses no integral
coroot-generation premise.

`coxeterTorusEnd` is the actual torus homomorphism
`t ↦ N t N⁻¹ t⁻¹`, where `N` is that ordered normalizer product. Its pullback on
all characters is injective by the kernel computation, applied to a difference
of two characters. The actual split-torus character criterion then proves
`coxeterTorusEnd_flat_and_surjective`: the underlying scheme morphism is flat
and surjective over any field, including finite and imperfect fields. The
hypothesis is only semisimplicity, so the result applies in particular to the
simply connected groups in the host task.

The conclusion is geometric faithful flatness. It does not assert surjectivity
on rational points, construct a cyclic gauge or field extension, construct
fundamental characters, or prove the canonical quotient isomorphism.
