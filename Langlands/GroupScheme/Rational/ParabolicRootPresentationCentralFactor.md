# Central homomorphisms factor through every standard Levi

`Langlands.GroupScheme.ParabolicRootPresentation.CentralLeviFactorStatement`
is proved by `centralLeviFactor`, which applies
`ParabolicRootPresentation.exists_levi_factor_of_isCentral`. It works over a
field `k`, with `G` affine over `k`. Let
`r : ParabolicRootPresentation p l a` present the parabolic `p : P ⟶ G`, the
rational Levi `l : M ⟶ P` and the split component `a`. Then every central
homomorphism `i : Z ⟶ G` (`IsCentral i`, on all test schemes) factors as
`i = j ≫ l ≫ p` for some `j : Z ⟶ M`. The group scheme `Z` is arbitrary and
need not be a torus.

The module also proves two supporting results:

- `IsCentral.range_le_torusCentralizer`: the image of a central homomorphism
  is contained in the centralizer `torusCentralizer t` of every torus
  `t : T ⟶ G`, on every test scheme.
- `ParabolicRootPresentation.range_le_levi_of_isCentral`: the image of a
  central homomorphism is contained in `SubgroupFunctor.range (l ≫ p)`.

## Provenance and scope

This is the standard fact that the centre of `G`, and in particular its
split component `A_G`, lies in every Levi subgroup. Lapid 2011 uses it
without comment in §8, printed p. 328 (PDF p. 337). There the Fourier
transform on `𝔞_G` writes the truncated pairing as an integral over
parameters `λ + μ` with `μ ∈ i𝔞_G^*`, which requires `A_G ⊆ A_M`. The source
is E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`.

Here it supplies the factorization hypothesis `j ≫ l ≫ p = i` of
`EisensteinContinuationCentralCovarianceStatement` (module
`AdelicEisensteinCentralCovariance`). It applies to the central split torus of
the product decomposition in `AdelicFullRationalQuotientProduct`. The
statement is about group schemes only; nothing adelic is claimed.

## Implemented proof

- **Torus centralizers.** For a point `g = y ≫ i` of the image, and any
  test morphism `c`, centrality of `i` puts `c ≫ y ≫ i` in the centre.
  So it commutes with every point `s ≫ t` of the torus
  (`commute_of_mem_center`).
- **Levi.** The compatibility field `levi_eq` identifies the image of `l ≫ p`
  with `standardLevi`. On each test scheme, `standardLevi` is the intersection
  of the dynamic centralizers of `ζ ≫ i_T`, over the standard cocharacters
  `ζ` of the maximal split torus `i_T`. A point centralizing the torus
  centralizes each of its cocharacters
  (`MaximalSplitSubgroup.torusCentralizer_le_centralizer_cocharacter`).
- **Factorization.** `l ≫ p` is a closed subgroup (composite of the Levi and
  parabolic closed subgroups), hence a monomorphism. So it represents its own
  image. `SubgroupFunctor.IsRepresentedBy.factorHom` then gives `j`, with
  `factorHom_comp` proving `j ≫ l ≫ p = i`.
