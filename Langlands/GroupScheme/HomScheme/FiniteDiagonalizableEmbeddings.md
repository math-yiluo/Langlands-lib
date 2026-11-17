# Quasi-affine schemes of finite diagonalizable embeddings

For a commutative ring `R`, a finite abelian group `M`, and an affine group
scheme `G` locally of finite presentation over `Spec R`, `embeddingModel R M G`
is an actual scheme with a universal closed embedding of the base change of
`D_R(M)` into the base change of `G`. For every scheme `T` over `Spec R`,
its `T`-points are in bijection with all closed group-scheme embeddings
`D_T(M) → G_T`. The parameter scheme is quasi-affine. In particular, finite
nonsmooth diagonalizable groups are included; smoothness of `G` is unnecessary.

This derived construction first uses `FiniteBialgebraHom.HomAlgebra` for the
finite free source algebra `R[M]` and the finitely presented Hopf coordinates
of `G`. `FiniteSource.isUniversal_universalFamily`, followed by the actual
Hopf-spectrum comparisons, proves universality of the affine Hom parameter
scheme on every scheme test.

On that affine parameter scheme, the pulled-back source is identified with
the literal diagonal Hopf spectrum. `FiniteDiagonalizableEmbeddingLocus`
provides the quasi-compact open where this universal map is a closed immersion.
Its exact all-test condition is preserved by the source isomorphism and the
published evaluation/pullback comparison. `ClosedEmbeddingModel.ofOpen`
restricts the actual Hom family to this open and retains its full universal
property for closed embeddings. Base change of the locally finitely presented
affine target gives the quasi-affineness conclusion for the open.

The accompanying generic `ClosedEmbeddingModel` record contains the scheme,
actual universal closed family, and bijectivity on all test schemes. Its
classifying map commutes with restriction. It introduces no representability
assumption beyond these explicit fields. This contribution constructs the
embedding parameter scheme; automorphism actions and normalizer orbit fibers
remain separate constructions.
