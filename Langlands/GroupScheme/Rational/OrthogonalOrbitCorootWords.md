# Coroot words over orthogonal sets of simple roots

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.OrthogonalOrbitCorootWords`, namespace
`Langlands.GroupScheme.SplitPinning`.

This module is a step toward `Z_G(S)(k) ⊆ G(k)^+` for quasi-split simply connected `G`.
Over a splitting field it writes products of coroot values along a Galois-stable,
pairwise orthogonal set of simple roots as words in Galois-fixed products of root
elements.

## Split level

Let `p` be a split pinning of an affine group `G` over a field `k`, and
`x : p.NormalizedSimpleRootParametrizations`.

- `rankData x a`: the rank-one relation data (module `Reductive.LinkedRootRationalRelation`)
  of the linked parametrization `(x a).linked` (module `Rational.NegativeRootPartner`).
  By `rankData_xp`, `rankData_xm` and `rankData_h`: its positive elements are the rational
  values of `x a`, its negative elements are the partner points `(x a).negPoint`, and its
  coroot values are the cocharacter points of the coroot of `a`.
- `rootsCommute_of_orthogonal x O hO`: if the simple roots in `O` are pairwise orthogonal
  (`p.rootDatum.IsOrthogonal`), the family `rankData x` over `O` satisfies
  `RankOneRelation.RootsCommute`. This is the published `orthogonalSimpleRootCommutation`,
  since positive and negative elements lie in `U_{±a}`.

## Galois level

The setting is that of `Rational.NegativeRootPartnerGalois`: fields `k ⊆ K`, `T` and
`i : T ⟶ G` over `k`, a split pinning `p` of `G_K` with `eT : p.torus ≅ T_K` and `hT`.
There are normalized simple-root maps `x`, compatible with a Galois action `ρ` on simple
roots (`hx : RootMapsGaloisCompatible`), and the root transport `hroot`. Let `O` be a set
of simple roots, stable under `ρ` (`hOs`), pairwise orthogonal (`hO`) and finite.

- `IsGaloisEquivariant ρ c`: the family `c : simple roots → K` satisfies
  `c (ρ σ a) = σ (c a)`.
- `orbitXp x O hO c` and `orbitXm x O hO c`: the products over `O` of the positive elements
  `x_a(c a)`, respectively of the negative partners `y_a(c a)`, via `RankOneRelation.prodHom`.
- `orbitXp_rationalConjugate` and `orbitXm_rationalConjugate`: for equivariant `c`, these
  products are fixed by every `rationalConjugate σ`. This is
  `RankOneRelation.map_prodHom_of_perm` with the permutation `ρ σ` of `O`. The factorwise
  identities are `RootMapsGaloisCompatible.rationalPoint` and
  `RootMapsGaloisCompatible.negPointFamily_rationalConjugate`.
- `orbitCoroot x O hO u`: the product over `O` of the coroot values `a^∨(u a)`.
- `orbitCoroot_eq_word`: it equals
  `(orbitXm (u⁻¹(u - 1)))⁻¹ * orbitXp 1 * orbitXm (u - 1) * (orbitXp u⁻¹)⁻¹`. This is
  `RankOneRelation.prodHom_h`.
- `IsGaloisEquivariant.word`: if `u` is equivariant, so are the four coefficient families
  of this word.

So for an equivariant unit family `u`, `orbitCoroot u` is a word in Galois-fixed products
of root elements. Their descent to `k`-points of relative root groups is a separate step.

## Provenance

Internal; assembles published commutation and Galois transport with the helper modules
cited above. Mathematically this is the orthogonal-orbit case of Steinberg's computation
`T(k) ⊆ G(k)^+` for quasi-split simply connected groups.
