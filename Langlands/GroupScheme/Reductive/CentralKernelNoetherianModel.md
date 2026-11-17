# Noetherian reductive models retaining central residue kernels

This internal derived construction works in any universe. Let `A` be an
arbitrary commutative ring, let `G` and `H` be reductive group schemes over
`Spec A`, and let `f : G ⟶ H` be locally quasi-finite, flat, and surjective.
Assume that the actual scheme-theoretic kernel of the homomorphism on every
canonical scheme-residue fibre is central in the source of that fibre.
`centralKernelNoetherianModel hG hH f hq hf hs hc` chooses a noetherian subring
of `A` and a model of this homomorphism over that subring retaining all these
properties. There is no noetherian assumption on `A`.

The returned `CentralKernelNoetherianModel f` extends the published
`NoetherianQuasiFiniteModel f`. Its fields give the coefficient subring and
its noetherian property; source and target group schemes and their reductivity;
a homomorphism which is locally quasi-finite, flat, and surjective; source
and target isomorphisms from the original groups to the pullbacks of these
models; and the equality identifying `f` with the pulled-back homomorphism
through these isomorphisms. The new `centralFibres` field states centrality
of the actual kernel of the model homomorphism after pullback to every
canonical scheme-residue field of the coefficient ring. All uses of centrality
are the full all-test-scheme predicate `IsCentral`.

The module supplies three comparisons. `centralFiberLocus_kernel_baseChange`
identifies the residue-centrality loci of the pulled-back kernel inclusion and
the inclusion of the actual pulled-back kernel. Its only base assumption is
that the new base is the spectrum of a commutative ring. It applies the canonical
kernel base-change isomorphism and its inclusion identity to the general
isomorphism-square comparison of centrality loci.
`centralFiberLocus_kernel_iso_square` identifies the kernel-inclusion loci under
a supplied commuting square of isomorphisms of the source and target groups.
It uses the actual `kernelSquareIso` and its inclusion identity.
`centralFiberLocus_kernel_eq_univ_iff` says that the kernel-inclusion locus is
the whole spectrum exactly when every actual canonical residue kernel is
central. This follows pointwise from the kernel base-change centrality
equivalence. These three comparisons need no reductivity or finiteness
assumptions.

`NoetherianQuasiFiniteModel.enlarge M T hT` extends any supplied noetherian
model along a finitely generated subalgebra `T` of `A` over its coefficient
ring. Its new coefficient subring is `T.toSubring`; finite generation makes
it noetherian. The groups and homomorphism are their actual pullbacks to
`Spec T`. Reductivity and the three map properties are stable under this base
change. The source and target recovery isomorphisms compose the old ones with
the inverse of the natural iterated-pullback comparison. Naturality of that
comparison proves the recovery equality.

`NoetherianQuasiFiniteModel.centralEnlargement M hc` applies the comparisons
to the recovery square for `M`, turning the supplied centrality on every
residue kernel of `f` into fullness of the centrality locus of the kernel
inclusion of `M.hom` after extension to `A`. The source model and its kernel
are affine and locally of finite type over the noetherian coefficient ring:
the source is reductive and the kernel inclusion is a closed immersion since
the target is affine and separated. The previously constructed
`centralFiberCoefficientModel` therefore chooses a finitely generated
coefficient subalgebra on which that locus is still the whole spectrum.
Enlarging `M` to this subalgebra and applying the kernel comparisons again
produces the new `centralFibres` field.

The final constructor first chooses the model supplied by the published
unconditional `reductiveQuasiFiniteNoetherianModel`, then applies
`centralEnlargement`. This is a derivation from existing noetherian approximation,
actual kernel and pullback comparisons, and constructible-locus coefficient
preservation; no external structural theorem is asserted here. The construction
retains the supplied residue-kernel centrality. It does not prove global
centrality or the full fibrewise central-isogeny criterion.
