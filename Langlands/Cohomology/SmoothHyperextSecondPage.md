# The second page of the hyperext spectral sequence for smooth representations

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextSpectralSequence` (`hyperextSpectralSequence`,
`secondPageIso`), `Langlands.Cohomology.HyperextSecondPage`
(`secondPageExtAddEquiv`), `Langlands.Cohomology.ExtRightDerived`
(`hasExt_smoothRep`, `smoothExtAddEquiv`) and
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`, `bifunctor`,
`extZeroIso`, `isZero_ext_succ_of_injective`, by Worker 13), and on
Mathlib's derived categories.

The module combines these results for the abelian category of smooth
representations. For an object `K` of a derived category of smooth
representations and a smooth representation `W` placed in degree zero, the
object in position `(p, q)` on page 2 of the hyperext spectral sequence is the
classical smooth Ext `Ext^p(H^{-q}(K), W)`: the `p`-th right derived functor
of equivariant Hom out of `H^{-q}(K)`, evaluated at `W`. This is the form of
the `E_2` terms in Harris's spectral sequences (4.4.1), (4.9) and (4.10.1).
Convergence of the spectral sequence is not proved.

## Setting

`R` is a commutative ring and `G` a topological group, both in universe `u`,
and `SmoothRep.{u, u, u} R G` is the abelian category of smooth
representations of `G` on `R`-modules in `Type u`, as in
`Langlands.Cohomology.SmoothExt`. The module assumes
`HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)` for an arbitrary universe
`w`, so that morphisms of `DerivedCategory (SmoothRep.{u, u, u} R G)` lie in
`Type w`. No such instance is chosen here. For example, Mathlib's
`HasDerivedCategory.standard`, a definition and not an instance, provides one
with `w = u + 1`.

`TStructure.t` is Mathlib's standard t-structure on the derived category,
`H^n` is `DerivedCategory.homologyFunctor _ n`, `(singleFunctor _ 0).obj W`
is `W` placed in degree zero, and `Q` is the localization functor from
cochain complexes indexed by `ℤ` to the derived category. `E_2^{p,q}`
below denotes the object in position `(p, q)` on page 2 of
`hyperextSpectralSequence TStructure.t K ((singleFunctor _ 0).obj W)`, an
object of `AddCommGrpCat.{w}`. `SmoothExt.ext R G V p` is the `p`-th right
derived functor of `Hom(V, -)` with values in `R`-modules.

## Declarations

| Declaration | Statement |
| --- | --- |
| `secondPageAddEquiv R G K W p q` | For `p : ℕ` and `q : ℤ`, `E_2^{p,q} ≃+ (SmoothExt.ext R G (H^{-q}(K)) p).obj W`. |
| `complexSecondPageAddEquiv R G L W p q` | For a cochain complex `L` indexed by `ℤ` and `E_2^{p,q}` formed for `K = Q.obj L`, `E_2^{p,q} ≃+ (SmoothExt.ext R G (L.homology (-q)) p).obj W`. |
| `secondPageZeroAddEquiv R G K W q` | `E_2^{0,q} ≃+ (H^{-q}(K) ⟶ W)`, the group of equivariant maps. |
| `isZero_secondPage_of_injective R G K W p q hp` (theorem) | If `W` is injective, then `E_2^{p,q}` is zero for integers `p > 0` and `q`. |

The equivalences are equivalences of underlying abelian groups; the targets
are `R`-modules, but no `R`-linearity is stated (see Scope).

## Proofs

- `secondPageAddEquiv`: with `HasExt.{u}` supplied by
  `ExtRightDerived.hasExt_smoothRep R G` (a theorem, used locally through
  `letI`), the composite of three steps:
  1. `secondPageIso TStructure.t K W₀ p q` of
     `Langlands.Cohomology.HyperextSpectralSequence`, with
     `W₀ = (singleFunctor _ 0).obj W`, viewed as an additive equivalence
     from `E_2^{p,q}` to the group of morphisms
     `heartPiece TStructure.t K q ⟶ W₀⟦p + q⟧`;
  2. `HyperextSecondPage.secondPageExtAddEquiv K W p q`, from that group to
     Mathlib's `Ext^p(H^{-q}(K), W)` in universe `u`;
  3. the inverse of `ExtRightDerived.smoothExtAddEquiv R G (H^{-q}(K)) W p`,
     from Mathlib's `Ext` to `(SmoothExt.ext R G (H^{-q}(K)) p).obj W`.
- `complexSecondPageAddEquiv`: `secondPageAddEquiv` for `K = Q.obj L`,
  followed by the isomorphism of smooth Ext induced in the first variable by
  Mathlib's `homologyFunctorFactors _ (-q)`, the natural isomorphism from
  `H^{-q}(Q.obj L)` to `L.homology (-q)`. The induced map is the image of the
  inverse of that component under the contravariant functor
  `SmoothExt.bifunctor R G p`, evaluated at `W`.
- `secondPageZeroAddEquiv`: `secondPageAddEquiv` at `p = 0`, followed by the
  component at `W` of `SmoothExt.extZeroIso R G (H^{-q}(K))`, the
  identification of the zeroth right derived functor of `Hom(H^{-q}(K), -)`
  with `Hom(H^{-q}(K), -)` itself (Mathlib's `rightDerivedZeroIsoSelf`).
- `isZero_secondPage_of_injective`: write `p = n + 1` with `n : ℕ`. By
  `SmoothExt.isZero_ext_succ_of_injective`, the module
  `(SmoothExt.ext R G (H^{-q}(K)) (n + 1)).obj W` is zero, hence has one
  element. Through `secondPageAddEquiv` the same holds for `E_2^{n+1,q}`,
  which is therefore a zero object of `AddCommGrpCat`.

Together with `HyperextSecondPage.isZero_secondPage_of_neg` (zero for
`p < 0`), the last theorem says that for injective `W` page 2 is concentrated
in the column `p = 0`, where it is `Hom(H^{-q}(K), W)`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`). The passages
below were read by Worker 61 in the rendered page scans.

- Proposition 4.4, printed p.309 (one-based PDF page 11), with `𝓛` a free
  `O/ℓ^m O`-module, `𝓛̃` the corresponding constant étale sheaf and
  `O_m = O/ℓ^m O`: "There is a spectral sequence of `O_m`-modules

  (4.4.1) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, O_m(n-1)), 𝒜_ℓ(GJ, 𝓛, K(m))) ⇒ H^{i+j}(S̄_{K(N,m)}, 𝓛̃)`.

  Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category
  of smooth `O_m[GJ]`-modules."
- Printed p.311 (one-based PDF page 13): the spectral sequence

  (4.9) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, O_m(n-1)), Hom(O_m[C_p/H_p]^M, 𝓛_m)) ⇒ H^{i+j}(S̄_{K(N)}, 𝓛̃_m)`,

  and Proposition 4.10, "There is a spectral sequence of `O`-modules

  (4.10.1) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.

  Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category
  of smooth `L_ℓ[GJ]`-modules."

Specialization (explanation only). Take `R = O_m` and `G = GJ` (the case
of (4.10.1), with `L_ℓ` coefficients, is analogous), `W` the coefficient
module (`𝒜_ℓ(GJ, 𝓛, K(m))`, respectively `Hom(O_m[C_p/H_p]^M, 𝓛_m)`), and
`K` an object of the derived category with
`H^{-q}(K) = H_c^{2(n-1)-q}(M̌_N, O_m(n-1))`. Then `secondPageAddEquiv` gives
`E_2^{p,q} ≃+ Ext^p(H_c^{2(n-1)-q}(M̌_N, O_m(n-1)), W)`, with `Ext^p` the
`p`-th right derived functor of `Hom` in the category of smooth
representations, which is Harris's `E_2^{i,j}` with `(i, j) = (p, q)`. When
`K` is the image of an explicit complex, `complexSecondPageAddEquiv` states
the same with the cohomology of that complex. None of this specialization is
formalized: no ring `O_m`, no group `GJ`, no complex `K` with the cohomology
of Harris's spaces and no coefficient module of Harris is defined here, and
the abutment `H^{i+j}(S̄_{K(N,m)}, 𝓛̃)` is not identified with the abutment
`Hom(K, W₀⟦p + q⟧)` of `Langlands.Cohomology.HyperextSpectralSequence`.
Harris's spectral sequences are spectral sequences of `O_m`-modules
(respectively `O`-modules); here the page-2 objects are abelian groups and the
identification with `Ext^p` is additive only.

The identification of `E_2` terms of a hyperext spectral sequence with
classical Ext is standard; the statements and proofs here are ours,
assembled from Mathlib and the Library.

## Scope

- Convergence of the spectral sequence, its differentials and its edge maps
  are not stated. As explained in `Langlands.Cohomology.HyperextSecondPage`,
  classically the spectral sequence converges when `K` is bounded; this is
  not formalized.
- All equivalences are additive. The targets are `R`-modules, but the
  equivalences are not shown to be `R`-linear; `E_2^{p,q}` itself is only an
  abelian group.
- No naturality in `K`, `L` or `W` is stated, and no compatibility of
  `complexSecondPageAddEquiv` or `secondPageZeroAddEquiv` with other
  identifications of `E_2`.
- The derived category instance `HasDerivedCategory.{w}` is a hypothesis; the
  results hold for each such instance, and `secondPageAddEquiv` does not
  compare the spectral sequences obtained from different instances.
- Only the second argument `W` placed in degree zero is treated, and only
  smooth representations in `SmoothRep.{u, u, u} R G`, with ring, group and
  carriers in one universe `u`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.309 and 311 read in the rendered page scans.

Dependencies: `Langlands.Cohomology.ExtRightDerived` and
`Langlands.Cohomology.HyperextSecondPage` (which import
`Langlands.Cohomology.SmoothExt` and
`Langlands.Cohomology.HyperextSpectralSequence`) and Mathlib, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
