# Torus and finite quotient of a multiplicative-type group

Author: Worker 1341. This is an internal construction from the existing actual
diagonalizable models, schematic images, and effective affine fpqc descent.
It does not use a classification converse or an additional literature theorem.

`HasTorusFiniteQuotient G` means that there are an actual group scheme `T`,
a homomorphism `j : T ⟶ G`, an actual group scheme `Q`, and a homomorphism
`q : G ⟶ Q` such that:

- `T` is a torus over the original field and `j` is a closed immersion.
- The structure map of `Q` is finite.
- `q` is flat, surjective, and locally of finite presentation, and its full
  represented kernel equals the all-test subgroup functor `range j`.

`IsMultiplicativeType.exists_torus_finiteQuotient` proves this predicate for
every finite-type multiplicative-type group over an arbitrary field, in every
universe `u`.

The proof first obtains affineness and commutativity from
`MultiplicativeTypeGeometry`. For a supplied splitting extension and actual
isomorphism `e : G_K ≅ D(Λ)`, the split construction
`Diagonalizable.exists_power_torus_finiteQuotient` supplies a natural number `n`,
a closed split torus `j_K : T_K ⟶ D(Λ)`, a schematically dominant map
`p : D(Λ) ⟶ T_K`, and a finite fppf quotient by `T_K`. Their composite is
the actual power endomorphism `[n]`.

Over the original field, take the actual schematic image `I` of `[n] : G ⟶ G`.
Flat base change preserves schematic dominance of its canonical projection.
The power-map base-change and naturality identities identify two closed
dominant factorizations of the same map on `G_K`: the extended image
factorization and the factorization through `T_K`, transported along `e`.
`SchematicImage.isoOfDominantFactorizations` therefore identifies `I_K`
with `T_K`. This gives `IsTorus I` using precisely that splitting extension.
Its inclusion into `G` is the canonical closed schematic-image inclusion.

The finite quotient of `D(Λ)`, precomposed with `e.hom`, has kernel equal to
the extended inclusion of `I`. The proof verifies this equality on every test
scheme, using the split kernel equality and the inverse identities of `e`.
`Descent.exists_affine_fppfQuotient` descends this supplied quotient to an actual
affine group scheme `R` and an actual fppf quotient `G ⟶ R`. Its recovery
isomorphism identifies `R_K` with the original finite target. Finiteness of
the structure morphism then descends along the fpqc field-extension map.

No smoothness, reducedness, perfectness, separability, or restriction on the
characteristic is assumed. The construction retains all torsion characters
and all finite scheme structure. It does not assert anisotropy of `T`; the
host maximal-split quotient theorem supplies that separate argument.
