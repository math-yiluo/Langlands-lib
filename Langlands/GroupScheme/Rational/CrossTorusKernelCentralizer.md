# Full character-kernel centralizer transport between acting groups

Work over any base scheme `B`, with commutative group schemes `S`, `S'`,
ambient group schemes `G`, `H`, and acting maps
`i : S.toGrp ⟶ G`, `j : S'.toGrp ⟶ H`. Supply an isomorphism `e : S ≅ S'`.
The transported character of `a : characterLattice S` is
`a' = characterLattice.congr e a = e.inv ≫ a`.

All kernels here are the full scheme-theoretic `RelativeRoot.characterKernel`.
They may be nonsmooth. The subgroup functor
`RelativeRoot.kernelCentralizer i a` requires commutation with every kernel
point after every refinement of each test scheme. The construction imposes no
field, affine, smoothness, reducedness, splitness, monomorphism, nonzero-character
or root-membership assumption.

## Full centralizer comparison

For an ambient homomorphism `f : G ⟶ H` satisfying

```text
i ≫ f = CommGroupScheme.groupHom e.hom ≫ j,
```

`comp_mem_kernelCentralizer_of_transport` proves that postcomposition with `f`
carries every point of the source full kernel centralizer into the target full
kernel centralizer at `a'`. This preservation result needs only an ambient
homomorphism.

For an ambient isomorphism `f : G ≅ H` with the same square for `f.hom`,
`kernelCentralizer_comap_of_transport` proves the literal equality

```text
(kernelCentralizer j a').comap f.hom = kernelCentralizer i a.
```

This is equality of subgroup functors on all objects of `Over B`, including
nonreduced test schemes. `mem_kernelCentralizer_transport_iff` exposes the
corresponding equivalence of membership predicates at every test.

`kernelCentralizerTransportEquiv e f h a U` is a multiplicative equivalence
between the two actual groups of centralizer points at any test scheme `U`.
Its forward map is `x ↦ x ≫ f.hom.hom.hom`, and its inverse is
`x ↦ x ≫ f.inv.hom.hom`. The two application lemmas record these exact ambient
maps. `kernelCentralizerTransportEquiv_naturality` states that the forward map
commutes with restriction along every morphism `V ⟶ U` of test schemes.

## The same transporting point

When `H = G`, supply a base point `g` and the square for the specific inner
isomorphism `G.innerIso g`. The specialization
`kernelCentralizerTransporterConjEquiv` uses that same `g`. Its forward and
inverse application formulas are respectively

```text
x ↦ g_U * x * g_U⁻¹,
x ↦ g_U⁻¹ * x * g_U,
```

where `g_U = G.constantPoint g U`. No alternative transporting point is chosen.

## Internal derivation

The proof uses `characterKernelCongr` and its inverse inclusion law from
`CrossTorusRootTransport`. Given an arbitrary target kernel point after an
arbitrary refinement, precompose it with the inverse full-kernel isomorphism.
Apply `RootSubgroup.mem_kernelCentralizer` to this source kernel point, then
postcompose its commutation identity with the ambient homomorphism. The kernel
inclusion identity and the supplied square identify the resulting kernel image
with the target kernel point's image. Thus all refinement quantifiers are
retained. Applying the argument to both inverse isomorphisms proves the comap
equality. Restriction of the ambient isomorphism gives the multiplicative
equivalence; associativity gives the refinement law. The existing inner
isomorphism formulas give both conjugation directions.

This is internal derived content in the cross-torus interface identified by
Worker 118. Its structural inputs remain the supplied acting-group and ambient
isomorphisms and their exact square. It does not prove centralizer
representability, smoothness or reductivity, torus existence or conjugacy,
root-subgroup realization, or a building or valuation comparison.
